import GNC.All
import GNC.Tools.Planner
import Verification.Policy

/-! Fail the build for unproved axioms, admitted proofs, native-decide axioms,
user unsafe/partial definitions or runtime replacements, and declarations
outside the checked environment. Lean-generated recursive runtime companions
are reported separately. Source modules are audited in every namespace.
-/
run_cmd Verification.Policy.check
