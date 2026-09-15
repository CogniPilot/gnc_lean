"""Materialize the flake's frozen sources in Lake's writable build directories.

This does not clone repositories or consult a global Lean installation. The
root path manifest prevents Lake from fetching transitive Git dependencies.
Mathlib's own manifest stays byte-for-byte intact for its compiled proof cache.
"""

import json
import pathlib
import shutil
import sys

spec = json.loads(pathlib.Path(sys.argv[1]).read_text())
root = pathlib.Path.cwd()
if not (root / "lakefile.toml").exists():
    raise SystemExit("Run gnc-setup in the gnc project directory.")

# Check the entire dependency closure against mathlib's upstream manifest.
upstream = json.loads((pathlib.Path(spec["mathlib"]["path"]) / "lake-manifest.json").read_text())
assert set(spec) == {"mathlib"} | {p["name"] for p in upstream["packages"]}
for package in upstream["packages"]:
    assert spec[package["name"]]["rev"] == package["rev"], package["name"]
assert (root / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.29.1"

packages = []
for name, dep in sorted(spec.items()):
    target = root / ".lake" / "packages" / name
    stamp = target / ".gnc-source"
    if target.exists() and not stamp.exists():
        raise SystemExit(f"{target} is not managed by this flake; remove it before setup.")
    elif target.exists() and stamp.read_text() != dep["path"]:
        raise SystemExit(f"{target} has an older pin; move it aside before setup.")
    elif not target.exists():
        shutil.copytree(dep["path"], target)
        for entry in [target, *target.rglob("*")]:
            if not entry.is_symlink():
                entry.chmod(entry.stat().st_mode | 0o200)
        stamp.write_text(dep["path"])
    packages.append({
        "type": "path", "scope": "", "name": name,
        "dir": f".lake/packages/{name}", "inherited": name != "mathlib",
        "configFile": "lakefile.lean" if (target / "lakefile.lean").exists() else "lakefile.toml",
        "manifestFile": "lake-manifest.json",
    })

manifest = {"version": "1.1.0", "packagesDir": ".lake/packages", "packages": packages,
            "name": "gnc", "lakeDir": ".lake"}
(root / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

# Upstream cache archives store dependency outputs under mathlib/.lake/packages.
# Point that directory at this project's dependency directory, without copying
# or modifying mathlib's release manifest.
mathlib_lake = root / ".lake/packages/mathlib/.lake"
mathlib_lake.mkdir(exist_ok=True)
nested_packages = mathlib_lake / "packages"
if not nested_packages.exists():
    nested_packages.symlink_to("../..", target_is_directory=True)

# The Lean widget modules include these exact release assets. Supplying them
# through Nix avoids a Git-based release lookup or an unpinned npm build.
assets = pathlib.Path(sys.argv[2])
js = root / ".lake/packages/proofwidgets/.lake/build/js"
if not js.exists():
    shutil.copytree(assets / "js", js)
    for entry in [js, *js.rglob("*")]:
        if not entry.is_symlink():
            entry.chmod(entry.stat().st_mode | 0o200)
