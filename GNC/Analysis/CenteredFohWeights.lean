import GNC.Analysis.DysonTranslation
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Time weights of the centered FOH rotation remainder. The normalized
integrated slope is zero initially and one at the endpoint. Keeping its
time dependence avoids assigning the endpoint error to the entire hold.
All rational coefficients below are definite integrals, not tolerances.
-/
noncomputable section
open Set
namespace GNC.Dyson

def centeredMass (t : ℝ) : ℝ := 4 * ∫ s in (0 : ℝ)..t, |s - 1/2|

theorem centeredMass_derivative (t : ℝ) :
    HasDerivAt centeredMass (4 * |t - 1/2|) t := by
  have hc : Continuous (fun s : ℝ => |s - 1/2|) := by fun_prop
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul 4

@[fun_prop] theorem centeredMass_continuous : Continuous centeredMass :=
  continuous_iff_continuousAt.mpr (fun t => (centeredMass_derivative t).continuousAt)

theorem centeredMass_zero : centeredMass 0 = 0 := by simp [centeredMass]
theorem centeredMass_one : centeredMass 1 = 1 := by
  rw [centeredMass, integral_abs_centered]
  norm_num

theorem centeredMass_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ centeredMass t := by
  unfold centeredMass
  exact mul_nonneg (by norm_num)
    (intervalIntegral.integral_nonneg ht (fun s _ => abs_nonneg _))

theorem centeredMass_left {t : ℝ} (ht : t ∈ Icc 0 (1/2)) :
    centeredMass t = 2*t - 2*t^2 := by
  have hi : (∫ s in (0 : ℝ)..t, |s-1/2|) = ∫ s in (0 : ℝ)..t, (1/2-s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change |s - 1/2| = 1/2-s
    rw [abs_of_nonpos (by linarith [hs.2, ht.2])]
    ring
  rw [centeredMass, hi, intervalIntegral.integral_sub
    (f := fun _ : ℝ => (1/2 : ℝ)) (g := fun s : ℝ => s) intervalIntegrable_const
    (continuous_id.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, integral_id]
  ring

theorem centeredMass_right {t : ℝ} (ht : 1/2 ≤ t) :
    centeredMass t = 2*t^2 - 2*t + 1 := by
  have hc : Continuous (fun s : ℝ => |s-1/2|) := by fun_prop
  have hi : (∫ s in (1/2 : ℝ)..t, |s-1/2|) =
      ∫ s in (1/2 : ℝ)..t, (s-1/2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact abs_of_nonneg (by linarith [hs.1])
  have hh := centeredMass_left (t := 1/2) ⟨by norm_num, le_rfl⟩
  unfold centeredMass at hh ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1/2)) (hc.intervalIntegrable (1/2) t), hi,
    intervalIntegral.integral_sub (f := fun s : ℝ => s) (g := fun _ : ℝ => (1/2 : ℝ))
      (continuous_id.intervalIntegrable _ _) intervalIntegrable_const]
  simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
  linarith

theorem centeredMass_cubic_split (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t in (0 : ℝ)..1, w t * centeredMass t ^ 3) =
      (∫ t in (0 : ℝ)..(1/2), w t * (2*t-2*t^2)^3) +
      ∫ t in (1/2 : ℝ)..1, w t * (2*t^2-2*t+1)^3 := by
  have hc : Continuous (fun t => w t * centeredMass t ^ 3) :=
    hw.mul (centeredMass_continuous.pow 3)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1/2)) (hc.intervalIntegrable (1/2) 1)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at ht
    dsimp only
    rw [centeredMass_left ht]
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    dsimp only
    rw [centeredMass_right ht.1]

theorem integral_polynomial_derivative (p : Polynomial ℝ) (a b : ℝ) :
    (∫ t in a..b, p.derivative.eval t) = p.eval b - p.eval a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => p.hasDerivAt t)
    (p.derivative.continuous.intervalIntegrable a b)

theorem centered_cubic_left_0 :
    (∫ t in (0 : ℝ)..(1/2), t^0 * (2*t-2*t^2)^3) = (1/35 : ℝ) := by
  let p : Polynomial ℝ := Polynomial.monomial 7 ((-8)/7:ℝ) + Polynomial.monomial 6 ((4)/1:ℝ) + Polynomial.monomial 5 ((-24)/5:ℝ) + Polynomial.monomial 4 ((2)/1:ℝ)
  have he (t : ℝ) : p.derivative.eval t = t^0 * (2*t-2*t^2)^3 := by
    norm_num [p, Polynomial.derivative_monomial]
    ring
  have h := integral_polynomial_derivative p 0 (1/2)
  simp_rw [he] at h
  convert h using 1
  norm_num [p]

theorem centered_cubic_right_0 :
    (∫ t in ((1/2) : ℝ)..1, t^0 * (2*t^2-2*t+1)^3) = (6/35 : ℝ) := by
  let p : Polynomial ℝ := Polynomial.monomial 7 ((8)/7:ℝ) + Polynomial.monomial 6 ((-4)/1:ℝ) + Polynomial.monomial 5 ((36)/5:ℝ) + Polynomial.monomial 4 ((-8)/1:ℝ) + Polynomial.monomial 3 ((6)/1:ℝ) + Polynomial.monomial 2 ((-3)/1:ℝ) + Polynomial.monomial 1 ((1)/1:ℝ)
  have he (t : ℝ) : p.derivative.eval t = t^0 * (2*t^2-2*t+1)^3 := by
    norm_num [p, Polynomial.derivative_monomial]
    ring
  have h := integral_polynomial_derivative p (1/2) 1
  simp_rw [he] at h
  convert h using 1
  norm_num [p]

theorem centeredMass_cubic_moment_0 :
    (∫ t in (0 : ℝ)..1, t^0 * centeredMass t ^ 3) = (1/5 : ℝ) := by
  rw [centeredMass_cubic_split (fun t => t^0) (by fun_prop), centered_cubic_left_0, centered_cubic_right_0]
  norm_num

theorem centered_cubic_left_1 :
    (∫ t in (0 : ℝ)..(1/2), t^1 * (2*t-2*t^2)^3) = (93/8960 : ℝ) := by
  let p : Polynomial ℝ := Polynomial.monomial 8 ((-1)/1:ℝ) + Polynomial.monomial 7 ((24)/7:ℝ) + Polynomial.monomial 6 ((-4)/1:ℝ) + Polynomial.monomial 5 ((8)/5:ℝ)
  have he (t : ℝ) : p.derivative.eval t = t^1 * (2*t-2*t^2)^3 := by
    norm_num [p, Polynomial.derivative_monomial]
    ring
  have h := integral_polynomial_derivative p 0 (1/2)
  simp_rw [he] at h
  convert h using 1
  norm_num [p]

theorem centered_cubic_right_1 :
    (∫ t in ((1/2) : ℝ)..1, t^1 * (2*t^2-2*t+1)^3) = (1293/8960 : ℝ) := by
  let p : Polynomial ℝ := Polynomial.monomial 8 ((1)/1:ℝ) + Polynomial.monomial 7 ((-24)/7:ℝ) + Polynomial.monomial 6 ((6)/1:ℝ) + Polynomial.monomial 5 ((-32)/5:ℝ) + Polynomial.monomial 4 ((9)/2:ℝ) + Polynomial.monomial 3 ((-2)/1:ℝ) + Polynomial.monomial 2 ((1)/2:ℝ)
  have he (t : ℝ) : p.derivative.eval t = t^1 * (2*t^2-2*t+1)^3 := by
    norm_num [p, Polynomial.derivative_monomial]
    ring
  have h := integral_polynomial_derivative p (1/2) 1
  simp_rw [he] at h
  convert h using 1
  norm_num [p]

theorem centeredMass_cubic_moment_1 :
    (∫ t in (0 : ℝ)..1, t^1 * centeredMass t ^ 3) = (99/640 : ℝ) := by
  rw [centeredMass_cubic_split (fun t => t^1) (by fun_prop), centered_cubic_left_1, centered_cubic_right_1]
  norm_num

theorem centered_cubic_left_2 :
    (∫ t in (0 : ℝ)..(1/2), t^2 * (2*t-2*t^2)^3) = (65/16128 : ℝ) := by
  let p : Polynomial ℝ := Polynomial.monomial 9 ((-8)/9:ℝ) + Polynomial.monomial 8 ((3)/1:ℝ) + Polynomial.monomial 7 ((-24)/7:ℝ) + Polynomial.monomial 6 ((4)/3:ℝ)
  have he (t : ℝ) : p.derivative.eval t = t^2 * (2*t-2*t^2)^3 := by
    norm_num [p, Polynomial.derivative_monomial]
    ring
  have h := integral_polynomial_derivative p 0 (1/2)
  simp_rw [he] at h
  convert h using 1
  norm_num [p]

theorem centered_cubic_right_2 :
    (∫ t in ((1/2) : ℝ)..1, t^2 * (2*t^2-2*t+1)^3) = (10037/80640 : ℝ) := by
  let p : Polynomial ℝ := Polynomial.monomial 9 ((8)/9:ℝ) + Polynomial.monomial 8 ((-3)/1:ℝ) + Polynomial.monomial 7 ((36)/7:ℝ) + Polynomial.monomial 6 ((-16)/3:ℝ) + Polynomial.monomial 5 ((18)/5:ℝ) + Polynomial.monomial 4 ((-3)/2:ℝ) + Polynomial.monomial 3 ((1)/3:ℝ)
  have he (t : ℝ) : p.derivative.eval t = t^2 * (2*t^2-2*t+1)^3 := by
    norm_num [p, Polynomial.derivative_monomial]
    ring
  have h := integral_polynomial_derivative p (1/2) 1
  simp_rw [he] at h
  convert h using 1
  norm_num [p]

theorem centeredMass_cubic_moment_2 :
    (∫ t in (0 : ℝ)..1, t^2 * centeredMass t ^ 3) = (1727/13440 : ℝ) := by
  rw [centeredMass_cubic_split (fun t => t^2) (by fun_prop), centered_cubic_left_2, centered_cubic_right_2]
  norm_num

theorem centeredMass_cubic_quadratic_integral (a b c : ℝ) :
    (∫ t in (0 : ℝ)..1, (a+b*t+c*t^2) * centeredMass t^3) =
      a/5 + b*(99/640) + c*(1727/13440) := by
  have he : (fun t : ℝ => (a+b*t+c*t^2) * centeredMass t^3) =
      fun t => (a*(t^0*centeredMass t^3)+b*(t^1*centeredMass t^3))+
        c*(t^2*centeredMass t^3) := by funext t; ring
  rw [he]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
  rw [centeredMass_cubic_moment_0, centeredMass_cubic_moment_1,
    centeredMass_cubic_moment_2]
  ring

def velocityWeight (n : ℕ) (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ((1-t)*a+t*b) * centeredMass t^n

def positionWeight (n : ℕ) (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1-t) * (((1-t)*a+t*b) * centeredMass t^n)

theorem velocityWeight_three (a b : ℝ) :
    velocityWeight 3 a b = (29*a+99*b)/640 := by
  have h := centeredMass_cubic_quadratic_integral a (b-a) 0
  convert h using 1
  · unfold velocityWeight
    congr 1
    funext t
    ring
  · ring

theorem positionWeight_three (a b : ℝ) :
    positionWeight 3 a b = (257*a+352*b)/13440 := by
  have h := centeredMass_cubic_quadratic_integral a (b-2*a) (a-b)
  convert h using 1
  · unfold positionWeight
    congr 1
    funext t
    ring
  · ring

theorem velocityWeight_three_same (a : ℝ) : velocityWeight 3 a a = a/5 := by
  rw [velocityWeight_three]
  ring

theorem positionWeight_three_same (a : ℝ) : positionWeight 3 a a = 29*a/640 := by
  rw [positionWeight_three]
  ring

theorem velocityWeight_three_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    velocityWeight 3 a b ≤ (a+b)/2 := by
  rw [velocityWeight_three]
  linarith

theorem positionWeight_three_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    positionWeight 3 a b ≤ (a+b)/2 := by
  rw [positionWeight_three]
  linarith

end GNC.Dyson
