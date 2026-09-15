import GNC.Analysis.FiniteAngleComparison

/-! Comparing concrete predictors using a complete physical error certificate.
This separate module avoids invalidating existing numerical certificate data
when adding generic comparison results. -/
noncomputable section
namespace GNC.FiniteAngleComparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A separation test for two concrete predictors and one complete physical
error certificate. The test does not assume a particular coordinate chart.
Taking k=1 requires separation greater than twice the certified error. -/
theorem certified_separation (p q baseline : E) {ε k : ℝ}
    (hk : 0 ≤ k) (hp : ‖p-q‖ ≤ ε)
    (hgap : (k+1)*ε < ‖q-baseline‖) :
    k*‖p-q‖ < ‖p-baseline‖ := by
  have ht := norm_add_le (q-p) (p-baseline)
  have hs : q-p+(p-baseline)=q-baseline := by abel
  rw [hs,norm_sub_rev q p] at ht
  have hm := mul_le_mul_of_nonneg_left hp hk
  nlinarith

end GNC.FiniteAngleComparison
