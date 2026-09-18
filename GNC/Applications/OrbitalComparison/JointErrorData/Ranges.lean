import GNC.Applications.OrbitalComparison.JointErrorData.Rho
import GNC.Applications.OrbitalComparison.JointErrorData.InverseOffset
import GNC.Applications.OrbitalComparison.JointErrorData.Model

/-! Uniform ranges derived from the actual checked coefficient profiles.
These constants are evaluations at normalized time one, not allowances. -/
namespace GNC.OrbitalComparison.JointErrorData
open ParameterPolynomial LieSTTOutput Planning.PolynomialKernel Set

def sigma : ℚ := 1/10
def rhoMaximum : ℚ := evaluate (rhoRange.bound 1) 1
def offsetMaximum : ℚ := evaluate (inverseOffsetRange.bound 1) 1

set_option maxHeartbeats 0 in
theorem uniform_ranges_checked :
    PolynomialOrder.nonnegative (rhoRange.bound 1) ∧
    PolynomialOrder.nonnegative (inverseOffsetRange.bound 1) ∧
    0<rhoMaximum ∧ 2*rhoMaximum<1 ∧ 0≤offsetMaximum ∧ offsetMaximum<1 := by
  decide +kernel

noncomputable section

theorem rho_uniform {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (value3 modelInput.rho x t)≤(rhoMaximum:ℝ) := by
  have h := BallNormProfile.certifies rhoRange rho rho_checked hx ht.1
  have h1 := h.trans (PolynomialOrder.value_le_endpoint _ uniform_ranges_checked.1 ht)
  have he := PolynomialOrder.value_at_rational (rhoRange.bound 1) 1
  norm_num only [Rat.cast_one] at he
  rw [he] at h1
  exact h1

theorem offset_uniform {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    |value modelInput.h x t|≤(offsetMaximum:ℝ) := by
  have hc : |value inverseOffset x t|≤‖DiskPolynomial.vectorValue ![inverseOffset] x t‖ := by
    simpa [DiskPolynomial.vectorValue,Real.norm_eq_abs] using
      PiLp.norm_apply_le (DiskPolynomial.vectorValue ![inverseOffset] x t) (0 : Fin 1)
  have h := hc.trans (BallNormProfile.certifies inverseOffsetRange ![inverseOffset]
    inverseOffset_checked hx ht.1)
  have h1 := h.trans (PolynomialOrder.value_le_endpoint _ uniform_ranges_checked.2.1 ht)
  have he := PolynomialOrder.value_at_rational (inverseOffsetRange.bound 1) 1
  norm_num only [Rat.cast_one] at he
  rw [he] at h1
  exact h1

theorem attitude_bound {x : Vec3} (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) :
    enorm x≤(sigma:ℝ) ∧ enorm x<2*Real.pi := by
  have hs : (0:ℝ)≤sigma := by norm_num [sigma]
  have hn := enorm_sq x
  change enorm x^2=x 0^2+x 1^2+x 2^2 at hn
  have hb : enorm x≤(sigma:ℝ) := by nlinarith [enorm_nonneg x]
  refine ⟨hb,hb.trans_lt ?_⟩
  norm_num only [sigma,Rat.cast_div,Rat.cast_ofNat]
  linarith [Real.two_le_pi]

end
end GNC.OrbitalComparison.JointErrorData
