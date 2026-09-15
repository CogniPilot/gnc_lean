import GNC.All
import GNC.Tools.Planner
import Verification.Policy

/-! Fresh machine-readable audit for scripts/verify.py. This is build tooling,
not a proof oracle. The report is emitted only after the audit succeeds. -/
run_cmd Verification.Policy.emitJson
