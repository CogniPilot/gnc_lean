"""Negative tests for the build's verification policy, in temporary modules.

Each failure must contain the audit's diagnostic, so a syntax/import failure
cannot accidentally count as a successful rejection. These are checks of the
audit tooling; they do not replace Lean's kernel checking of proof terms.
"""
from pathlib import Path
import json
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def main():
    cases = [
        ("GNC/LibraryClient", "import GNC.All\ndef main : IO Unit := pure ()", None),
        ("GNC/Positive", "theorem valid : True := True.intro", None),
        ("GNC/Applications/Positive", "theorem valid : True := True.intro", None),
        ("GNC/Applications/Admitted", "theorem admitted : False := by sorry", "forbidden axiom sorryAx"),
        ("GNC/Applications/OtherNamespace", "namespace Outside\naxiom hidden : False\nend Outside",
         "Unproved project axiom"),
        ("GNC/Admitted", "theorem admitted : False := by sorry", "forbidden axiom sorryAx"),
        ("GNC/AdmittedDefinition", "def hidden : Nat := False.elim (by sorry)",
         "forbidden axiom sorryAx"),
        ("GNC/AdmittedType", "def hidden (h : (by sorry : Prop)) : Nat := 0",
         "forbidden axiom sorryAx"),
        ("GNC/AdmittedOpaque", "opaque hidden : False := by sorry", "forbidden axiom sorryAx"),
        ("GNC/UnusedAxiom", "axiom unused : False", "Unproved project axiom"),
        ("GNC/PrivateAxiom", "private axiom hidden : False", "Unproved project axiom"),
        ("GNC/OtherNamespace", "namespace Outside\naxiom hidden : False\nend Outside",
         "Unproved project axiom"),
        ("External", "axiom GNC.hidden : False", "Unproved project axiom"),
        ("Transitive", "axiom outside : False\ntheorem GNC.usesOutside : False := outside",
         "Project depends on forbidden axiom outside"),
        ("GNC/Unsafe", "unsafe def unsafeValue : Nat := 0", "Unsafe or partial project declaration"),
        ("GNC/Partial", "partial def loop (n : Nat) : Nat := loop n",
         "Unsafe or partial project declaration"),
        ("GNC/Replacement", "def runtimeValue : Nat := 1\n"
         "@[implemented_by runtimeValue] def logicalValue : Nat := 0",
         "Unchecked project runtime replacement"),
        ("GNC/Foreign", '@[extern "unchecked_runtime"] def foreignValue : Nat := 0',
         "Unchecked project runtime replacement"),
        ("GNC/Native", "theorem unchecked : 1 + 1 = (2 : Nat) := by native_decide",
         "Unproved project axiom"),
        ("GNC/Recursive", "def total : Nat → Nat\n | 0 => 0\n | n+1 => total n + 1\n"
         "theorem total_zero : total 0 = 0 := rfl", None),
    ]
    with tempfile.TemporaryDirectory(prefix="gnc-audit-") as directory:
        for module, declaration, expected in cases:
            path = Path(directory, module + ".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("import Verification.Policy\nimport Lean.Elab.Tactic.Decide\n"
                            + declaration + "\nrun_cmd Verification.Policy.check\n")
            process = subprocess.run(
                ["lake", "env", "lean", "--root=" + directory, str(path)],
                cwd=ROOT, capture_output=True, text=True,
            )
            output = process.stdout + process.stderr
            if expected is None:
                assert process.returncode == 0 and "Axiom audit passed" in output, (module, output)
            else:
                assert process.returncode != 0 and expected in output, (module, output)
    print(json.dumps({"audit_cases": len(cases), "status": "passed"}, indent=2))


if __name__ == "__main__":
    main()
