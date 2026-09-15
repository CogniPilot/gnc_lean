"""Adversarial checks of release coverage and stale-report detection.

These test the build attestation tooling; Lean remains the proof checker.
The fixtures include newly added unimported files, not just modified hashes.
"""
import json
import shutil
import subprocess
from pathlib import Path
import tempfile
from unittest import TestCase, TestLoader, TextTestRunner
import sys

from verify import check_module_coverage, check_report, source_hashes
from check_structure import structure_errors


class ReleaseTests(TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="gnc-release-tests-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        for path in ["GNC/All.lean", "GNC/Core.lean", "GNC/Applications.lean", "GNC/Verification.lean", "flake.nix", "flake.lock",
                     "lakefile.toml", "lake-manifest.json", "lean-toolchain", "docs/VERIFICATION.md",
                     "GNC/Example.lean", "GNC/Applications/Example.lean", "nix/lean.nix"]:
            file = self.root / path
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text("fixture\n")
        (self.root/'GNC/All.lean').write_text('import GNC.Core\nimport GNC.Applications\n')
        (self.root/'GNC/Core.lean').write_text('import GNC.Example\n')
        (self.root/'GNC/Applications.lean').write_text('import GNC.Applications.Example\n')
        (self.root/'GNC/Verification.lean').write_text('import GNC.All\n')
        self.modules = ['GNC.All', 'GNC.Core', 'GNC.Example', 'GNC.Applications', 'GNC.Applications.Example']
        self.record = self.root / "record.json"
        self.record.write_text(json.dumps({"status": "passed", "checked_at_utc": "fixture",
                                           "source_sha256": source_hashes(self.root)}))

    def test_matching_snapshot(self):
        self.assertEqual(check_report(self.record, self.root)["status"], "source snapshot matches")

    def test_changed_proof(self):
        (self.root / "GNC/Example.lean").write_text("changed\n")
        with self.assertRaisesRegex(RuntimeError, "changed:.*GNC/Example.lean"):
            check_report(self.record, self.root)

    def test_new_unimported_proof(self):
        (self.root / "GNC/Unimported.lean").write_text("axiom hidden : False\n")
        with self.assertRaisesRegex(RuntimeError, "added:.*GNC/Unimported.lean"):
            check_report(self.record, self.root)

    def test_removed_proof(self):
        (self.root / "GNC/Example.lean").unlink()
        with self.assertRaisesRegex(RuntimeError, "missing:.*GNC/Example.lean"):
            check_report(self.record, self.root)

    def test_changed_environment(self):
        (self.root / "nix/lean.nix").write_text("changed\n")
        with self.assertRaisesRegex(RuntimeError, "changed:.*lean.nix"):
            check_report(self.record, self.root)

    def test_failed_report(self):
        report = json.loads(self.record.read_text())
        report["status"] = "failed"
        self.record.write_text(json.dumps(report))
        with self.assertRaisesRegex(RuntimeError, "did not pass"):
            check_report(self.record, self.root)

    def test_library_inventory(self):
        check_module_coverage({"source_modules": self.modules}, ["GNC"], self.root)

    def test_unloaded_library_module(self):
        with self.assertRaisesRegex(RuntimeError, "missing:.*GNC.Example"):
            check_module_coverage({"source_modules": ["GNC"]}, ["GNC"], self.root)

    def test_unexpected_module(self):
        with self.assertRaisesRegex(RuntimeError, "unexpected:.*Unexpected.Example"):
            check_module_coverage({"source_modules": self.modules+['Unexpected.Example']},
                                  ["GNC"], self.root)

    def test_missing_application_aggregate(self):
        with self.assertRaisesRegex(RuntimeError, "missing:.*GNC.Applications"):
            check_module_coverage({'source_modules': [m for m in self.modules if m!='GNC.Applications']},
                                  ['GNC'], self.root)

    def test_missing_application_proof(self):
        with self.assertRaisesRegex(RuntimeError, "missing:.*GNC.Applications.Example"):
            check_module_coverage({'source_modules': [m for m in self.modules if m!='GNC.Applications.Example']},
                                  ['GNC'], self.root)

    def test_complete_structure(self):
        self.assertEqual(structure_errors(self.root)[0], [])

    def test_application_not_exported(self):
        (self.root/'GNC/All.lean').write_text('import GNC.Core\n')
        self.assertIn('Not exported by GNC: GNC.Applications.Example', structure_errors(self.root)[0])

    def test_core_cannot_import_application(self):
        (self.root/'GNC/Example.lean').write_text('import GNC.Applications.Example\n')
        self.assertIn('Core imports an application: GNC.Example -> GNC.Applications.Example',
                      structure_errors(self.root)[0])

    def test_proof_outside_gnc(self):
        (self.root/'extra').mkdir()
        (self.root/'extra/Stray.lean').write_text('theorem stray : True := True.intro\n')
        self.assertIn('Proof outside GNC: extra/Stray.lean', structure_errors(self.root)[0])

    def test_no_root_lean_files(self):
        (self.root/'Stray.lean').write_text('theorem stray : True := True.intro\n')
        self.assertIn('Proof outside GNC: Stray.lean', structure_errors(self.root)[0])

    def test_no_lean_scripts(self):
        (self.root/'scripts').mkdir()
        (self.root/'scripts/Stray.lean').write_text('theorem stray : True := True.intro\n')
        self.assertIn('Proof outside GNC: scripts/Stray.lean', structure_errors(self.root)[0])

    def test_cli_is_separate_but_covered(self):
        (self.root/'GNC/Tools').mkdir()
        (self.root/'GNC/Tools/Planner.lean').write_text('import GNC.Core\n')
        (self.root/'GNC/Verification.lean').write_text('import GNC.All\nimport GNC.Tools.Planner\n')
        self.assertEqual(structure_errors(self.root)[0], [])
        (self.root/'GNC/Verification.lean').write_text('import GNC.All\n')
        self.assertIn('Not covered by default verification target: GNC.Tools.Planner', structure_errors(self.root)[0])

    def test_math_cannot_import_cli(self):
        (self.root/'GNC/Tools').mkdir()
        (self.root/'GNC/Tools/Planner.lean').write_text('import GNC.Core\n')
        (self.root/'GNC/All.lean').write_text('import GNC.Core\nimport GNC.Applications\nimport GNC.Tools.Planner\n')
        self.assertIn('Mathematics imports executable tooling: GNC.All -> GNC.Tools.Planner',
                      structure_errors(self.root)[0])

    def test_import_cycle(self):
        (self.root/'GNC/Example.lean').write_text('import GNC.Core\n')
        self.assertTrue(any('Import cycle:' in error for error in structure_errors(self.root)[0]))



class LakeCacheTests(TestCase):
    def test_reuse_transfer_and_dependency_invalidation(self):
        with tempfile.TemporaryDirectory(prefix="gnc-lake-cache-") as directory:
            root = Path(directory) / "original"
            (root / "Cache").mkdir(parents=True)
            (root / "lakefile.toml").write_text(
                'name = "cache_check"\ndefaultTargets = ["Cache"]\n'
                '[[lean_lib]]\nname = "Cache"\nglobs = ["Cache.+"]\n')
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.29.1\n")
            (root / "Cache/A.lean").write_text("def Cache.value : Nat := 1\n")
            (root / "Cache/B.lean").write_text("theorem Cache.independent : True := True.intro\n")
            (root / "Cache/C.lean").write_text(
                "import Cache.A\ntheorem Cache.exact : Cache.value = 1 := rfl\n")

            def build(workspace):
                process = subprocess.run(["lake", "build"], cwd=workspace, capture_output=True, text=True)
                self.assertEqual(process.returncode, 0, process.stdout + process.stderr)

            def stamps(workspace):
                return {name: (workspace / ".lake/build/lib/lean/Cache" /
                               f"{name}.olean").stat().st_mtime_ns for name in ["A", "B", "C"]}

            build(root)
            first = stamps(root)
            build(root)
            self.assertEqual(stamps(root), first, "Unchanged proofs were recompiled")
            copied = Path(directory) / "copied"
            shutil.copytree(root, copied)
            build(copied)
            self.assertEqual(stamps(copied), first, "Transferred proof cache was discarded")
            (copied / "Cache/A.lean").write_text("def Cache.value : Nat := 2\n")
            invalid = subprocess.run(["lake", "build"], cwd=copied, capture_output=True, text=True)
            output = invalid.stdout + invalid.stderr
            self.assertNotEqual(invalid.returncode, 0, "A stale dependent proof was accepted")
            self.assertIn("error: Cache/C.lean:2:0: Not a definitional equality", output)
            self.assertEqual((copied / ".lake/build/lib/lean/Cache/B.olean").stat().st_mtime_ns, first["B"])
            (copied / "Cache/C.lean").write_text(
                "import Cache.A\ntheorem Cache.exact : Cache.value = 2 := rfl\n")
            build(copied)
            after = stamps(copied)
            self.assertNotEqual(after["A"], first["A"], "Changed module was not rebuilt")
            self.assertNotEqual(after["C"], first["C"], "Dependent theorem was not rebuilt")
            self.assertEqual(after["B"], first["B"], "Unrelated theorem was recompiled")


if __name__ == "__main__":
    result = TextTestRunner(stream=sys.stderr).run(TestLoader().loadTestsFromModule(sys.modules[__name__]))
    if not result.wasSuccessful():
        sys.exit(1)
    print(json.dumps({"release_cases": result.testsRun, "status": "passed"}, indent=2))
