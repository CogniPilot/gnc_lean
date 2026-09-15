import GNC.Control.ThrustIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact thrust moments for a finite burn. Net velocity increment alone
does not determine the endpoint position, even for continuous nonnegative
acceleration. No impulsive or small-attitude approximation is used. -/
noncomputable section
open Set MeasureTheory
namespace GNC.FiniteBurn
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def velocityMoment (a : ℝ → E) (T : ℝ) : E := ∫ t in (0:ℝ)..T, a t
def positionMoment (a : ℝ → E) (T : ℝ) : E := ∫ t in (0:ℝ)..T, (T-t) • a t

theorem velocity_endpoint (a v : ℝ → E) {T : ℝ} (hT : 0 ≤ T)
    (ha : Continuous a) (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (a t) t) :
    v T = v 0+velocityMoment a T := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hv t (by simpa only [uIcc_of_le hT] using ht)) (ha.intervalIntegrable 0 T)
  dsimp [velocityMoment]
  rw [hi]
  abel

/-- Integration of p+(T-t)v cancels the velocity term and exposes the
first thrust moment directly, avoiding an assumed double-integral formula. -/
theorem position_endpoint (a p v : ℝ → E) {T : ℝ} (hT : 0 ≤ T)
    (ha : Continuous a) (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (a t) t) :
    p T = p 0+T • v 0+positionMoment a T := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt (fun s => p s+(T-s) • v s) ((T-t) • a t) t := by
    convert (hp t ht).add (((hasDerivAt_const t T).sub (hasDerivAt_id t)).smul (hv t ht)) using 1
    dsimp
    module
  have hc : Continuous (fun s => (T-s) • a s) := (continuous_const.sub continuous_id).smul ha
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le hT] using ht)) (hc.intervalIntegrable 0 T)
  simp only [sub_self, zero_smul, add_zero, sub_zero] at hi
  dsimp [positionMoment]
  rw [hi]
  abel

/-- Unit physical thrust direction preserves scalar effort; net vector
impulse can be smaller because directions need not agree throughout the burn. -/
theorem net_impulse_le_effort (a : ℝ → ℝ) (q : ℝ → Vec3) {T : ℝ}
    (hT : 0 ≤ T) (ha : Continuous a) (hq : Continuous q)
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ a t) (hunit : ∀ t ∈ Icc 0 T, q t ⬝ᵥ q t = 1) :
    enorm (velocityMoment (fun t => a t • q t) T) ≤ ∫ t in (0:ℝ)..T, a t := by
  have hi := ThrustSupport.enorm_integral_le (fun t => a t • q t) hT ((ha.smul hq).intervalIntegrable 0 T)
  have he : (∫ t in (0:ℝ)..T, enorm (a t • q t)) = ∫ t in (0:ℝ)..T, a t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
    change enorm (a t • q t) = a t
    rw [enorm_smul, ThrustSupport.unit_enorm _ (hunit t ht'), abs_of_nonneg (hpos t ht'), mul_one]
  exact he ▸ hi

/-- Two smooth nonnegative thrust histories on [0,1] have the same net
delta-v (and scalar effort), but different displacement moments. -/
theorem equal_deltaV_different_position :
    velocityMoment (fun t : ℝ => 2*(1-t)) 1 = 1 ∧
    velocityMoment (fun t : ℝ => 2*t) 1 = 1 ∧
    positionMoment (fun t : ℝ => 2*(1-t)) 1 = (2/3 : ℝ) ∧
    positionMoment (fun t : ℝ => 2*t) 1 = (1/3 : ℝ) := by
  have hp : ∀ A B C : ℝ, (∫ t in (0:ℝ)..1, A+B*t+C*t^2) = A+B/2+C/3 := by
    intro A B C
    have h0 : IntervalIntegrable (fun t : ℝ => A+B*t) volume 0 1 :=
      (show Continuous (fun t : ℝ => A+B*t) by fun_prop).intervalIntegrable 0 1
    have h1 : IntervalIntegrable (fun t : ℝ => C*t^2) volume 0 1 :=
      (show Continuous (fun t : ℝ => C*t^2) by fun_prop).intervalIntegrable 0 1
    have h2 : IntervalIntegrable (fun t : ℝ => B*t) volume 0 1 :=
      (show Continuous (fun t : ℝ => B*t) by fun_prop).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add h0 h1,
      intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 1) h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    norm_num [integral_pow]
    ring
  have e₁ : (fun t : ℝ => 2*(1-t)) = fun t => 2+(-2)*t+0*t^2 := by funext t; ring
  have e₂ : (fun t : ℝ => 2*t) = fun t => 0+2*t+0*t^2 := by funext t; ring
  have e₃ : (fun t : ℝ => (1-t)*(2*(1-t))) = fun t => 2+(-4)*t+2*t^2 := by funext t; ring
  have e₄ : (fun t : ℝ => (1-t)*(2*t)) = fun t => 0+2*t+(-2)*t^2 := by funext t; ring
  unfold velocityMoment positionMoment
  simp only [smul_eq_mul]
  rw [e₁, e₂, e₃, e₄, hp, hp, hp, hp]
  norm_num

theorem no_position_from_deltaV :
    ¬ ∃ f : ℝ → ℝ, ∀ a : ℝ → ℝ, Continuous a →
      (∀ t ∈ Icc (0:ℝ) 1, 0 ≤ a t) → positionMoment a 1 = f (velocityMoment a 1) := by
  rintro ⟨f, hf⟩
  have he := hf (fun t => 2*(1-t)) (by fun_prop) (by intro t ht; nlinarith [ht.2])
  have hl := hf (fun t => 2*t) (by fun_prop) (by intro t ht; nlinarith [ht.1])
  obtain ⟨hv₁, hv₂, hp₁, hp₂⟩ := equal_deltaV_different_position
  rw [hv₁, hp₁] at he
  rw [hv₂, hp₂] at hl
  linarith

/-- A constant bounded pointing offset accumulates linearly during a burn.
Thus an attitude-loop BIBO certificate alone is not an infinite-horizon
BIBO certificate for the integrated thrust error. -/
theorem constant_pointing_accumulation (q n : Vec3) {accel T : ℝ}
    (ha : 0 ≤ accel) (hT : 0 ≤ T) :
    enorm (velocityMoment (fun _ => accel • q) T-
      velocityMoment (fun _ => accel • n) T) = T*accel*enorm (q-n) := by
  simp only [velocityMoment, intervalIntegral.integral_const, sub_zero,
    ← smul_sub, smul_smul, enorm_smul, abs_of_nonneg (mul_nonneg hT ha)]

end GNC.FiniteBurn
