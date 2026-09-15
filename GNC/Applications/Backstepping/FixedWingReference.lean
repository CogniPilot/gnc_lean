import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-! A seventh-degree fixed-wing reference, following Lévine Chapter 14.
This proves reference kinematics, not an aerodynamic allocation theorem.
-/
noncomputable section
namespace GNC.FixedWingReference

def blend (s : ℝ) : ℝ := 35*s^4-84*s^5+70*s^6-20*s^7
def blend1 (s : ℝ) : ℝ := 140*s^3-420*s^4+420*s^5-140*s^6
def blend2 (s : ℝ) : ℝ := 420*s^2-1680*s^3+2100*s^4-840*s^5
def blend3 (s : ℝ) : ℝ := 840*s-5040*s^2+8400*s^3-4200*s^4

theorem blend_derivative (s : ℝ) : HasDerivAt blend (blend1 s) s := by
  unfold blend blend1
  convert (((((hasDerivAt_id s).pow 4).const_mul 35).sub
    (((hasDerivAt_id s).pow 5).const_mul 84)).add
    (((hasDerivAt_id s).pow 6).const_mul 70)).sub
    (((hasDerivAt_id s).pow 7).const_mul 20) using 1 <;> simp only [id_eq] <;> ring

theorem blend1_derivative (s : ℝ) : HasDerivAt blend1 (blend2 s) s := by
  unfold blend1 blend2
  convert (((((hasDerivAt_id s).pow 3).const_mul 140).sub
    (((hasDerivAt_id s).pow 4).const_mul 420)).add
    (((hasDerivAt_id s).pow 5).const_mul 420)).sub
    (((hasDerivAt_id s).pow 6).const_mul 140) using 1 <;> simp only [id_eq] <;> ring

theorem blend2_derivative (s : ℝ) : HasDerivAt blend2 (blend3 s) s := by
  unfold blend2 blend3
  convert (((((hasDerivAt_id s).pow 2).const_mul 420).sub
    (((hasDerivAt_id s).pow 3).const_mul 1680)).add
    (((hasDerivAt_id s).pow 4).const_mul 2100)).sub
    (((hasDerivAt_id s).pow 5).const_mul 840) using 1 <;> simp only [id_eq] <;> ring

theorem endpoint_jets :
    blend 0 = 0 ∧ blend 1 = 1 ∧
    blend1 0 = 0 ∧ blend1 1 = 0 ∧
    blend2 0 = 0 ∧ blend2 1 = 0 ∧
    blend3 0 = 0 ∧ blend3 1 = 0 := by
  norm_num [blend, blend1, blend2, blend3]

theorem blend1_factor (s : ℝ) : blend1 s = 140*s^3*(1-s)^3 := by
  unfold blend1; ring

theorem blend2_factor (s : ℝ) : blend2 s = 420*s^2*(1-s)^2*(1-2*s) := by
  unfold blend2; ring

theorem blend1_nonneg {s : ℝ} (hs : s ∈ Set.Icc 0 1) : 0 ≤ blend1 s := by
  rw [blend1_factor]
  exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs.1 _))
    (pow_nonneg (sub_nonneg.mpr hs.2) _)

theorem blend1_bound {s : ℝ} (hs : s ∈ Set.Icc 0 1) : blend1 s ≤ 35/16 := by
  have hu : 0 ≤ s*(1-s) := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
  have hb : s*(1-s) ≤ 1/4 := by nlinarith [sq_nonneg (s-1/2)]
  have hcube := pow_le_pow_left₀ hu hb 3
  rw [blend1_factor]
  nlinarith [hcube]

theorem blend2_bound {s : ℝ} (hs : s ∈ Set.Icc 0 1) : |blend2 s| ≤ 105/4 := by
  have hu : 0 ≤ s*(1-s) := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
  have hb : s*(1-s) ≤ 1/4 := by nlinarith [sq_nonneg (s-1/2)]
  have hsquare := pow_le_pow_left₀ hu hb 2
  have ha : |1-2*s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [blend2_factor, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 420),
    abs_of_nonneg (sq_nonneg s), abs_of_nonneg (sq_nonneg (1-s))]
  calc
    420*s^2*(1-s)^2*|1-2*s| ≤ 420*s^2*(1-s)^2 := by
      nlinarith [mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 420*s^2*(1-s)^2)]
    _ ≤ 105/4 := by nlinarith [hsquare]

def lateral (D T t : ℝ) : ℝ := D*blend (t/T)
def lateralVelocity (D T t : ℝ) : ℝ := D/T*blend1 (t/T)
def lateralAcceleration (D T t : ℝ) : ℝ := D/T^2*blend2 (t/T)
def lateralJerk (D T t : ℝ) : ℝ := D/T^3*blend3 (t/T)

theorem lateral_derivative (D T t : ℝ) :
    HasDerivAt (lateral D T) (lateralVelocity D T t) t := by
  convert ((blend_derivative (t/T)).comp t
    ((hasDerivAt_id t).div_const T)).const_mul D using 1 <;>
    dsimp [lateral, lateralVelocity] <;> ring

theorem lateralVelocity_derivative (D T t : ℝ) :
    HasDerivAt (lateralVelocity D T) (lateralAcceleration D T t) t := by
  convert ((blend1_derivative (t/T)).comp t
    ((hasDerivAt_id t).div_const T)).const_mul (D/T) using 1 <;>
    dsimp [lateralVelocity, lateralAcceleration] <;> ring

theorem lateralAcceleration_derivative (D T t : ℝ) :
    HasDerivAt (lateralAcceleration D T) (lateralJerk D T t) t := by
  convert ((blend2_derivative (t/T)).comp t
    ((hasDerivAt_id t).div_const T)).const_mul (D/T^2) using 1 <;>
    dsimp [lateralAcceleration, lateralJerk] <;> ring

theorem maneuver_endpoints (D T : ℝ) (hT : T ≠ 0) :
    lateral D T 0 = 0 ∧ lateral D T T = D ∧
    lateralVelocity D T 0 = 0 ∧ lateralVelocity D T T = 0 ∧
    lateralAcceleration D T 0 = 0 ∧ lateralAcceleration D T T = 0 ∧
    lateralJerk D T 0 = 0 ∧ lateralJerk D T T = 0 := by
  norm_num [lateral, lateralVelocity, lateralAcceleration, lateralJerk, hT,
    blend, blend1, blend2, blend3]

/-- A constant positive forward component prevents zero reference speed. -/
theorem reference_speed_nonzero (V D T t : ℝ) (hV : 0 < V) :
    0 < V^2 + lateralVelocity D T t ^ 2 := by
  positivity

/-- Continuous-time bounds for the concrete 100 m / 30 s lane change.
These are interval-wide real inequalities, not sampled maxima. -/
theorem example_derivative_bounds {t : ℝ} (ht : t ∈ Set.Icc 0 30) :
    |lateralVelocity 100 30 t| ≤ 175/24 ∧
    |lateralAcceleration 100 30 t| ≤ 35/12 := by
  have hs : t/30 ∈ Set.Icc (0:ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have h1 := blend1_nonneg hs
  have h2 := blend1_bound hs
  have h3 := blend2_bound hs
  constructor
  · norm_num [lateralVelocity, abs_mul, abs_of_nonneg h1]
    nlinarith
  · norm_num [lateralAcceleration, abs_mul]
    nlinarith

/-- An order-eleven alternative matches endpoint derivatives through five,
which avoids the fourth/fifth-derivative mismatch of a merely C³ join when
the reference is lifted through moment and servo dynamics. -/
def servoBlend : Polynomial ℝ :=
  462*Polynomial.X^6-1980*Polynomial.X^7+3465*Polynomial.X^8-
    3080*Polynomial.X^9+1386*Polynomial.X^10-252*Polynomial.X^11

theorem servoBlend_endpoints :
    servoBlend.eval 0 = 0 ∧ servoBlend.eval 1 = 1 := by
  norm_num [servoBlend]

theorem servoBlend_endpoint_derivatives (k : ℕ) (hk : k ∈ Finset.Icc 1 5) :
    ((Polynomial.derivative^[k]) servoBlend).eval 0 = 0 ∧
    ((Polynomial.derivative^[k]) servoBlend).eval 1 = 0 := by
  simp only [Finset.mem_Icc] at hk
  obtain ⟨hklo, hkhi⟩ := hk
  interval_cases k <;>
    norm_num [servoBlend, Function.iterate_succ_apply, Polynomial.derivative_sub,
      Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow]

theorem servoBlend_derivative (k : ℕ) (s : ℝ) :
    HasDerivAt (fun t => ((Polynomial.derivative^[k]) servoBlend).eval t)
      (((Polynomial.derivative^[k]) servoBlend).derivative.eval s) s :=
  Polynomial.hasDerivAt _ _

end GNC.FixedWingReference
