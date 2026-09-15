"""Build and audit GNC using Lake's incremental proof cache.

Run: nix develop --command python scripts/verify.py
Use --fresh only for an explicit isolated rebuild of all project proofs.
The output is a snapshot of this source tree, not a proof of physical model
accuracy, compiler correctness, or completion of the paper formalizations.
"""
from datetime import datetime, timezone
from hashlib import sha256
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / ".lake/verification"


def lean_sources(root):
    for directory, children, files in os.walk(root):
        children[:] = [p for p in children if p not in {".lake", ".git"}]
        for file in files:
            if file.endswith(".lean"):
                yield Path(directory, file)


def dependencies():
    """Detect changes to copied release sources, even with an unchanged stamp."""
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    spec = json.loads(Path(os.environ["GNC_DEPENDENCY_SPEC"]).read_text())
    assert {p["name"] for p in manifest["packages"]} == set(spec), "Dependency set differs from flake"
    result = {}
    for package in manifest["packages"]:
        local = ROOT / package["dir"]
        pinned = Path(spec[package["name"]]["path"])
        assert (local / ".gnc-source").read_text().strip() == str(pinned), "Dependency stamp differs from flake"
        assert pinned.is_dir() and str(pinned).startswith("/nix/store/"), pinned
        originals = {p.relative_to(pinned) for p in lean_sources(pinned)}
        actual = {p.relative_to(local) for p in lean_sources(local)}
        assert actual == originals, f"Unexpected/missing Lean source in {package['name']}"
        for relative in originals | {Path("lean-toolchain"), Path("lake-manifest.json"), Path("lakefile.toml")}:
            source = pinned / relative
            if source.is_file():
                assert (local / relative).read_bytes() == source.read_bytes(), \
                    f"Modified pinned dependency: {package['name']}/{relative}"
        result[package["name"]] = {"source": str(pinned), "lean_files": len(originals)}
    return result


def run(label, command, cwd=ROOT):
    print(f"Checking {label}…", flush=True)
    log_path = OUTPUT / (label + ".log")
    error_path = OUTPUT / (label + ".stderr.log")
    with log_path.open("w") as stdout, error_path.open("w") as stderr:
        process = subprocess.run(command, cwd=cwd, stdout=stdout, stderr=stderr, text=True)
    output = log_path.read_text()
    with log_path.open("a") as stream:
        stream.write(error_path.read_text())
    error_path.unlink()
    if process.returncode:
        raise RuntimeError(f"{label} failed; see {log_path}")
    return output


def source_modules(scopes, root=ROOT):
    """Mathematical modules; audit tooling has its own Lake source root."""
    modules = set()
    for scope in scopes:
        for path in (root / scope).rglob("*.lean"):
            relative = path.relative_to(root)
            if relative.parts[1] == "Verification" or relative == Path("GNC/Verification.lean"):
                continue
            modules.add(str(relative.with_suffix("")).replace("/", "."))
    return modules


def check_module_coverage(audit, scopes, root=ROOT):
    expected = source_modules(scopes, root)
    actual = set(audit["source_modules"])
    if expected != actual:
        raise RuntimeError(f"Lean module coverage differs from source tree; "
                           f"missing: {sorted(expected - actual)}; "
                           f"unexpected: {sorted(actual - expected)}")


def check_library(workspace, *, fresh):
    """Let Lake validate inputs and reuse all up-to-date proof artifacts."""
    modules = sorted(source_modules(["GNC"], workspace))
    artifacts = {module: workspace / ".lake/build/lib/lean" /
                 (module.replace(".", "/") + ".olean") for module in modules}
    before = {module: path.stat().st_mtime_ns for module, path in artifacts.items()
              if path.is_file()}
    run("library", ["lake", "build", "Verification"], cwd=workspace)
    for module, artifact in artifacts.items():
        assert artifact.is_file(), f"Build omitted {module}"
    reused = sum(before.get(module) == path.stat().st_mtime_ns
                 for module, path in artifacts.items())
    audit = json.loads(run("audit",
                           ["lake", "env", "lean", "--root=GNC", "GNC/Verification/Report.lean"],
                           cwd=workspace))
    check_module_coverage(audit, ["GNC"], workspace)
    regressions = {
        label: json.loads(run(label, ["python", "scripts/" + script], cwd=workspace))
        for label, script in [("audit-tests", "check_audit.py"),
                              ("release-tests", "check_release.py"),
                              ("planner-tests", "check_planner.py")]
    }
    return ({"status": "passed", "mode": "fresh" if fresh else "incremental",
             "source_modules": len(modules),
             "source_modules_recompiled": len(modules) - reused,
             "source_modules_reused": reused,
             "project_cache_reused": reused > 0,
             "released_dependency_cache_reused": True}, audit, regressions)


def fresh_library():
    """Explicit clean rebuild; retain its checked artifacts in Lake's cache."""
    hashes = source_hashes()
    with tempfile.TemporaryDirectory(prefix="fresh-library-", dir=OUTPUT) as directory:
        workspace = Path(directory)
        for folder in ["GNC", "scripts"]:
            shutil.copytree(ROOT / folder, workspace / folder)
        for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
            shutil.copy2(ROOT / name, workspace / name)
        (workspace / ".lake").mkdir()
        (workspace / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)
        result = check_library(workspace, fresh=True)
        assert source_hashes() == hashes, "Source changed during verification; rerun on a stable tree"
        # Both directories are on the same filesystem. Keep the old cache until
        # all checks pass, and restore it if installing the fresh cache fails.
        current = ROOT / ".lake/build"
        previous = workspace / "previous-build"
        if current.exists():
            current.rename(previous)
        try:
            (workspace / ".lake/build").rename(current)
        except OSError:
            if previous.exists():
                previous.rename(current)
            raise
        return result


def source_hashes(root=ROOT):
    sources = [p for folder in ["GNC", "scripts"]
               for p in (root / folder).rglob("*")
               if p.suffix in {".lean", ".py", ".jl", ".nix", ".c", ".cpp", ".h"} and "__pycache__" not in p.parts]
    sources += [root / p for p in ["flake.nix", "flake.lock", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
                "docs/VERIFICATION.md"]]
    sources += list((root / "nix").rglob("*.nix"))
    sources += list((root / "nix").rglob("*.patch"))
    return {str(p.relative_to(root)): sha256(p.read_bytes()).hexdigest()
            for p in sorted(sources)}


def check_report(report_path, root=ROOT):
    """Check a dated attestation's exact source set without rerunning proofs.

    This detects additions as well as changed/deleted files. It does not
    authenticate a report or turn numerical/application claims into proofs.
    """
    report = json.loads(Path(report_path).read_text())
    if report.get("status") != "passed":
        raise RuntimeError("The verification report did not pass")
    expected = report["source_sha256"]
    actual = source_hashes(root)
    changed = sorted(path for path in expected.keys() & actual.keys()
                     if expected[path] != actual[path])
    missing, added = sorted(expected.keys() - actual.keys()), sorted(actual.keys() - expected.keys())
    if changed or missing or added:
        raise RuntimeError(f"Verification report is stale; changed: {changed}; "
                           f"missing: {missing}; added: {added}")
    return {"status": "source snapshot matches", "source_files": len(actual),
            "report": str(report_path), "checked_at_utc": report["checked_at_utc"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--fresh", action="store_true",
                      help="Rebuild all project proofs from scratch, then retain the checked cache")
    mode.add_argument("--check-report", type=Path,
                      help="Check that a passed report matches every current verification source")
    args = parser.parse_args()
    if args.check_report is not None:
        print(json.dumps(check_report(args.check_report), indent=2))
        return
    OUTPUT.mkdir(parents=True, exist_ok=True)
    report_path = OUTPUT / "report.json"
    report_path.write_text(json.dumps({"status": "running"}) + "\n")
    try:
        if not __debug__:
            raise RuntimeError("Verification must run without Python optimization (-O)")
        lean_binary = Path(shutil.which("lean")).resolve()
        assert lean_binary == Path(os.environ["GNC_LEAN_BIN"]).resolve(), "Use the flake's Lean binary"
        hashes = source_hashes()
        print("Checking pinned dependency sources…", flush=True)
        pins = dependencies()
        run("structure", ["python", "scripts/check_structure.py"])
        run("repository", ["python", "scripts/check_repository.py"])
        # Lake checks source/dependency traces before reusing any project
        # artifact. The audit and regressions inspect that completed build.
        build, audit, regressions = (
            fresh_library() if args.fresh else check_library(ROOT, fresh=False))
        assert source_hashes() == hashes, "Source changed during verification; rerun on a stable tree"
        assert dependencies() == pins, "Dependency sources changed during verification"
        report = {
            "schema_version": 5,
            "status": "passed",
            "checked_at_utc": datetime.now(timezone.utc).isoformat(),
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "lean_binary": str(lean_binary), "library_build": build,
            "audit": audit, "audit_regression": regressions["audit-tests"],
            "release_regression": regressions["release-tests"],
            "planner_regression": regressions["planner-tests"], "dependencies": pins,
            "source_sha256": hashes,
            "claim": "All GNC theorem declarations are kernel-checked under their stated hypotheses.",
            "exclusions": ["physical model accuracy", "compiler and floating-point correctness",
                           "complete aircraft/orbit certification", "all statements in source papers"],
        }
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        print(f"Verification passed: {report_path}")
    except Exception as error:
        report_path.write_text(json.dumps({"status": "failed", "error": str(error)}, indent=2) + "\n")
        raise


if __name__ == "__main__":
    main()
