import GNC.Analysis.Transition
import GNC.Control.IntegralTube
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A posteriori propagation bounds from the actual differential defect.
The exact transition transports the error. No convergence of an infinite
Magnus series, nor a skew generator, is assumed. -/
noncomputable section
open Set MeasureTheory
namespace GNC.DefectBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
abbrev End := E →L[ℝ] E

def kernel (Φ : ℝ → (End (E := E))ˣ) (t s : ℝ) : End (E := E) :=
  (Φ t).val*((Φ s)⁻¹).val

theorem kernel_continuous (Φ : ℝ → (End (E := E))ˣ) (A : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t) (t : ℝ) :
    Continuous (kernel Φ t) := by
  have hi : Continuous (fun s => ((Φ s)⁻¹).val) := continuous_iff_continuousAt.mpr
    (fun s => (ForcedResponse.inverse_derivative Φ A hΦ s).continuousAt)
  exact continuous_const.mul hi

/-- Exact endpoint error representation, with a nonzero initial error allowed.
The approximate solution's defect is z' - A z - f. -/
theorem error_formula (Φ : ℝ → (End (E := E))ˣ) (A : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (x z f d : ℝ → E) {a b : ℝ} (hab : a ≤ b) (hd : Continuous d)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (A t (x t)+f t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (A t (z t)+f t+d t) t) :
    z b-x b = kernel Φ b a (z a-x a)+∫ s in a..b, kernel Φ b s (d s) := by
  have hc := ForcedResponse.integrand_continuous Φ A hΦ d hd
  have hder (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => ((Φ s)⁻¹).val (z s-x s))
        (ForcedResponse.integrand Φ d t) t := by
    convert (ForcedResponse.inverse_derivative Φ A hΦ t).clm_apply
      ((hz t ht).sub (hx t ht)) using 1
    simp [ForcedResponse.integrand, ContinuousLinearMap.mul_apply, map_sub, map_add]
    module
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hder t (by simpa only [uIcc_of_le hab] using ht))
    (hc.intervalIntegrable a b)
  have he := congrArg (fun y => (Φ b).val y) hi
  simp only [map_sub, ForcedResponse.cancel] at he
  rw [← (Φ b).val.intervalIntegral_comp_comm (hc.intervalIntegrable a b)] at he
  have he' : (∫ s in a..b, kernel Φ b s (d s)) = z b-x b-kernel Φ b a (z a-x a) := by
    simpa only [kernel, ContinuousLinearMap.mul_apply, ForcedResponse.integrand, map_sub] using he
  exact (sub_eq_iff_eq_add.mp he'.symm).trans (add_comm _ _)

theorem error_bound (Φ : ℝ → (End (E := E))ˣ) (A : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (x z f d : ℝ → E) {a b R gain : ℝ} (hab : a ≤ b) (hd : Continuous d)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (A t (x t)+f t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (A t (z t)+f t+d t) t)
    (hR : 0 ≤ R) (hbound : ∀ s ∈ Icc a b, ‖d s‖ ≤ R)
    (hgain : (∫ s in a..b, ‖kernel Φ b s‖) ≤ gain) :
    ‖z b-x b‖ ≤ ‖kernel Φ b a (z a-x a)‖+gain*R := by
  rw [error_formula Φ A hΦ x z f d hab hd hx hz]
  exact (norm_add_le _ _).trans (add_le_add_right
    (IntegralTube.response_bound (kernel Φ b) d hab (kernel_continuous Φ A hΦ b)
      hd hR hbound hgain) _)

/-- A verified order-p differential-defect envelope gives an order-(p+1)
local error. The constant and envelope must actually be proved for the chosen
continuous interpolant; an observed refinement slope is insufficient. -/
theorem polynomial_defect_bound (Φ : ℝ → (End (E := E))ˣ) (A : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (x z f d : ℝ → E) (p : ℕ) {h C M : ℝ} (hh : 0 ≤ h)
    (hd : Continuous d) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hx : ∀ t ∈ Icc 0 h, HasDerivAt x (A t (x t)+f t) t)
    (hz : ∀ t ∈ Icc 0 h, HasDerivAt z (A t (z t)+f t+d t) t)
    (hinit : z 0 = x 0)
    (hbound : ∀ s ∈ Icc 0 h, ‖d s‖ ≤ C*s^p)
    (hkernel : ∀ s ∈ Icc 0 h, ‖kernel Φ h s‖ ≤ M) :
    ‖z h-x h‖ ≤ M*C*h^(p+1)/(p+1) := by
  rw [error_formula Φ A hΦ x z f d hh hd hx hz, hinit, sub_self, map_zero, zero_add]
  have hk := kernel_continuous Φ A hΦ h
  have hf : Continuous (fun s => kernel Φ h s (d s)) := hk.clm_apply hd
  have hp : Continuous (fun s : ℝ => (M*C)*s^p) := continuous_const.mul (continuous_id.pow p)
  have hb : ∀ s ∈ Icc 0 h, ‖kernel Φ h s (d s)‖ ≤ (M*C)*s^p := by
    intro s hs
    exact ((kernel Φ h s).le_opNorm (d s)).trans
      ((mul_le_mul (hkernel s hs) (hbound s hs) (norm_nonneg _) hM).trans_eq (by ring))
  have hi := intervalIntegral.integral_mono_on (μ := volume) hh
    (hf.norm.intervalIntegrable 0 h) (hp.intervalIntegrable 0 h) hb
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun s => kernel Φ h s (d s)) hh
  have hh' := hn.trans hi
  simpa only [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero p),
    sub_zero, mul_div_assoc] using hh'

end GNC.DefectBound
