import GNC.Control.ThrustSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-! Continuous coherent-burn support and drift from actual direction-rate
dynamics. All norms here are Euclidean; the Pi-space supremum norm is not
used as a substitute for physical thrust magnitude. -/
noncomputable section
open Matrix MeasureTheory Set
namespace GNC.ThrustSupport

def dotMap (q : Vec3) : Vec3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun h => h ⬝ᵥ q
    map_add' := fun _ _ => add_dotProduct _ _ _
    map_smul' := fun _ _ => by simp [smul_dotProduct] }

theorem integral_pairing (h : ℝ → Vec3) (q : Vec3) {a b : ℝ}
    (hh : IntervalIntegrable h volume a b) :
    (∫ t in a..b, h t ⬝ᵥ q) = (∫ t in a..b, h t) ⬝ᵥ q :=
  (dotMap q).intervalIntegral_comp_comm hh

theorem integral_cap_support (h : ℝ → Vec3) (n q : Vec3) {a b κ ell : ℝ}
    (hh : IntervalIntegrable h volume a b)
    (hq : q ∈ Cap n κ) (hell : 0 ≤ ell) :
    (∫ t in a..b, h t ⬝ᵥ q) ≤ dualBound n (∫ t in a..b, h t) κ ell := by
  rw [integral_pairing h q hh]
  exact cap_support_bound n _ q κ ell hq hell

def euclideanEquiv : Vec3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm

theorem enorm_integral_le (h : ℝ → Vec3) {a b : ℝ} (hab : a ≤ b)
    (hh : IntervalIntegrable h volume a b) :
    enorm (∫ t in a..b, h t) ≤ ∫ t in a..b, enorm (h t) := by
  change ‖euclideanEquiv.toContinuousLinearMap (∫ t in a..b, h t)‖ ≤ _
  rw [← euclideanEquiv.toContinuousLinearMap.intervalIntegral_comp_comm hh]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-- Integrating first cannot increase the isotropic support radius. -/
theorem coherent_ball_le_pointwise (h : ℝ → Vec3) (n : Vec3) {a b δ : ℝ}
    (hab : a ≤ b) (hh : IntervalIntegrable h volume a b) (hδ : 0 ≤ δ) :
    ballBound n (∫ t in a..b, h t) δ ≤
      (∫ t in a..b, h t ⬝ᵥ n)+δ*(∫ t in a..b, enorm (h t)) := by
  rw [integral_pairing h n hh]
  exact add_le_add_right (mul_le_mul_of_nonneg_left (enorm_integral_le h hab hh) hδ) _

/-- A bound on angular rate gives a within-burn chord drift bound, provided
the physical direction obeys q'=omega × q and remains a unit vector. -/
theorem direction_drift (q omega : ℝ → Vec3) {a b beta : ℝ}
    (hq : ∀ t ∈ Icc a b, HasDerivAt q (omega t ⨯₃ q t) t)
    (hunit : ∀ t ∈ Icc a b, q t ⬝ᵥ q t = 1)
    (hrate : ∀ t ∈ Ico a b, enorm (omega t) ≤ beta) :
    ∀ t ∈ Icc a b, enorm (q t-q a) ≤ beta*(t-a) := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s => euclideanEquiv (q s))
        (euclideanEquiv (omega t ⨯₃ q t)) (Icc a b) t :=
    (euclideanEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hq t ht)).hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Ico a b) : ‖euclideanEquiv (omega t ⨯₃ q t)‖ ≤ beta := by
    change enorm (omega t ⨯₃ q t) ≤ beta
    have h := cross_enorm_le (omega t) (q t)
    rw [unit_enorm _ (hunit t (Ico_subset_Icc_self ht)), mul_one] at h
    exact h.trans (hrate t ht)
  exact norm_image_sub_le_of_norm_deriv_le_segment' hd hb

/-- A changing direction adds a separate support allowance to the coherent
initial offset. This is the continuous coefficient used in the fuel LP. -/
theorem integral_support_with_drift (h q : ℝ → Vec3) (epsilon : ℝ → ℝ)
    (n : Vec3) {a b kappa ell : ℝ} (hab : a ≤ b)
    (hh : Continuous h) (hq : Continuous q) (he : Continuous epsilon)
    (hcap : q a ∈ Cap n kappa) (hell : 0 ≤ ell)
    (hdrift : ∀ t ∈ Icc a b, enorm (q t-q a) ≤ epsilon t) :
    (∫ t in a..b, h t ⬝ᵥ q t) ≤
      dualBound n (∫ t in a..b, h t) kappa ell+
        ∫ t in a..b, enorm (h t)*epsilon t := by
  have hc : Continuous (fun t => enorm (h t)) := (euclideanEquiv.continuous.comp hh).norm
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    ((hh.dotProduct (hq.sub continuous_const)).intervalIntegrable a b)
    ((hc.mul he).intervalIntegrable a b) (fun t ht =>
      (dot_le_enorm (h t) (q t-q a)).trans
        (mul_le_mul_of_nonneg_left (hdrift t ht) (enorm_nonneg (h t))))
  simp_rw [dotProduct_sub] at hi
  rw [intervalIntegral.integral_sub ((hh.dotProduct hq).intervalIntegrable a b)
    ((hh.dotProduct continuous_const).intervalIntegrable a b)] at hi
  simp only [Pi.mul_apply] at hi
  have hb := integral_cap_support h n (q a) (hh.intervalIntegrable a b) hcap hell
  linarith

end GNC.ThrustSupport
