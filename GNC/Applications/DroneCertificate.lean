import GNC.Analysis.ConstantSecondOrderBound
import GNC.Analysis.SwitchedPrimitive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-! The jet-drone mini example: constant thrust, depleting mass, fixed tilt.
The field is state-independent, so the curvature is zero and the certificate
collapses to quadrature of the defect (`h_0 = τ^2/2`). The frozen-mass and
truncated variable-mass predictors are both certified by the general
second-order certificate; every constant is rational. -/
noncomputable section
namespace GNC.DroneCertificate
open Set SwitchedPrimitive PolynomialSupersolution

/-- Thrust force (N). -/ def F : ℝ := 200
/-- Initial mass (kg). -/ def mi : ℝ := 12
/-- Burn horizon (s). -/ def T : ℝ := 8
/-- Fuel flow times horizon (kg): 0.1*8. -/ def sT : ℝ := 4/5

/-- Clamped normalized time; continuous on all of ℝ. -/
def tc (t : ℝ) : ℝ := max 0 (min 1 t)
/-- Mass along the burn, clamped outside [0,1]. -/
def mass (t : ℝ) : ℝ := mi - sT * tc t
/-- Reciprocal-mass lift. -/
def wMass (t : ℝ) : ℝ := 1 / mass t
/-- Degree-five geometric truncation of the reciprocal mass. -/
def wTrunc5 (t : ℝ) : ℝ := (1/mi) * ∑ k ∈ Finset.range 6, (t/15)^k

/-- Frozen-mass predictor defect, normalized second derivative. -/
def defectA (θ t : ℝ) : ℝ := T^2 * F * Real.cos θ * (wMass t - 1/mi)
/-- Truncated variable-mass predictor defect. -/
def defectB (θ t : ℝ) : ℝ := T^2 * F * Real.cos θ * (wMass t - wTrunc5 t)

/-- Velocity of the frozen-mass error. -/
def velA (θ : ℝ) : ℝ → ℝ := antiderivative (defectA θ)
/-- Position of the frozen-mass error. -/
def errA (θ : ℝ) : ℝ → ℝ := antiderivative (velA θ)
/-- Velocity of the truncated variable-mass error. -/
def velB (θ : ℝ) : ℝ → ℝ := antiderivative (defectB θ)
/-- Position of the truncated variable-mass error. -/
def errB (θ : ℝ) : ℝ → ℝ := antiderivative (velB θ)

theorem tc_mem (t : ℝ) : tc t ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem tc_eq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : tc t = t := by
  simp [tc, min_eq_right ht.2, max_eq_right ht.1]

theorem mass_pos (t : ℝ) : 0 < mass t := by
  have h1 := (tc_mem t).2
  have hle : (4/5 : ℝ) * tc t ≤ 4/5 :=
    calc (4/5 : ℝ) * tc t ≤ (4/5) * 1 := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 4/5 := mul_one _
  simp only [mass, mi, sT]
  linarith

theorem tc_continuous : Continuous tc :=
  continuous_const.max (continuous_const.min continuous_id)

theorem mass_continuous : Continuous mass :=
  continuous_const.sub (continuous_const.mul tc_continuous)

theorem wMass_continuous : Continuous wMass := by
  show Continuous fun t : ℝ => (1:ℝ) / mass t
  exact Continuous.div₀ continuous_const mass_continuous
    (fun t => ne_of_gt (mass_pos t))

theorem wTrunc5_continuous : Continuous wTrunc5 := by
  show Continuous (fun t : ℝ => (1/mi) * ∑ k ∈ Finset.range 6, (t/15)^k)
  apply continuous_const.mul
  apply continuous_finset_sum
  intro k _
  exact (continuous_id.div_const 15).pow k

theorem defectA_continuous (θ : ℝ) : Continuous (defectA θ) :=
  continuous_const.mul (wMass_continuous.sub continuous_const)

theorem defectB_continuous (θ : ℝ) : Continuous (defectB θ) :=
  continuous_const.mul (wMass_continuous.sub wTrunc5_continuous)

theorem velA_hasDeriv (θ : ℝ) (t : ℝ) :
    HasDerivAt (velA θ) (defectA θ t) t :=
  antiderivative_derivative (defectA_continuous θ) t

theorem errA_hasDeriv (θ : ℝ) (t : ℝ) :
    HasDerivAt (errA θ) (velA θ t) t :=
  antiderivative_derivative (antiderivative_continuous (defectA_continuous θ)) t

theorem velB_hasDeriv (θ : ℝ) (t : ℝ) :
    HasDerivAt (velB θ) (defectB θ t) t :=
  antiderivative_derivative (defectB_continuous θ) t

theorem errB_hasDeriv (θ : ℝ) (t : ℝ) :
    HasDerivAt (errB θ) (velB θ t) t :=
  antiderivative_derivative (antiderivative_continuous (defectB_continuous θ)) t

theorem errA_zero (θ : ℝ) : errA θ 0 = 0 := by simp [errA, antiderivative]
theorem velA_zero (θ : ℝ) : velA θ 0 = 0 := by simp [velA, antiderivative]
theorem errB_zero (θ : ℝ) : errB θ 0 = 0 := by simp [errB, antiderivative]
theorem velB_zero (θ : ℝ) : velB θ 0 = 0 := by simp [velB, antiderivative]

theorem cos_bounds {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36)) :
    0 ≤ Real.cos θ ∧ Real.cos θ ≤ 1 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  obtain ⟨h1, h2⟩ := hθ
  constructor
  · apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
  · exact Real.cos_le_one θ

/-- On the burn, the reciprocal mass equals the rational expression. -/
theorem wMass_eq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    wMass t = 1/(12 - (4/5)*t) := by
  simp only [wMass, mass, mi, sT, tc_eq t ht]

/-- On the burn, the reciprocal mass exceeds its initial value. -/
theorem wMass_ge_initial (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (1/12 : ℝ) ≤ wMass t := by
  have h1 : (0:ℝ) < 12 - (4/5)*t := by have h := ht.2; linarith
  have h2 : 12 - (4/5)*t ≤ 12 := by have h := ht.1; linarith
  rw [wMass_eq t ht]
  exact one_div_le_one_div_of_le h1 h2

/-- On the burn, the reciprocal mass stays below its final value. -/
theorem wMass_le_final (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    wMass t ≤ (5/56 : ℝ) := by
  have h1 : (0:ℝ) < 56/5 := by norm_num
  have h2 : (56/5 : ℝ) ≤ 12 - (4/5)*t := by have h := ht.2; linarith
  rw [wMass_eq t ht]
  calc (1:ℝ)/(12 - (4/5)*t) ≤ 1/(56/5) := one_div_le_one_div_of_le h1 h2
    _ = 5/56 := by norm_num

/-- The frozen-mass defect bound: 1600/21 = 76.19 m in normalized units. -/
theorem defectA_bound {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36))
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : |defectA θ t| ≤ 1600/21 := by
  obtain ⟨hc0, hc1⟩ := cos_bounds hθ
  have hlo := wMass_ge_initial t ht
  have hhi := wMass_le_final t ht
  have hd0 : (0:ℝ) ≤ wMass t - 1/mi := by simp only [mi]; linarith
  have hd1 : wMass t - 1/mi ≤ 1/168 := by simp only [mi]; linarith
  have hnn : (0:ℝ) ≤ defectA θ t := by
    simp only [defectA, T, F]
    exact mul_nonneg (mul_nonneg (by norm_num) hc0) hd0
  rw [abs_of_nonneg hnn]
  calc defectA θ t = (8^2 * 200) * Real.cos θ * (wMass t - 1/mi) := by
        simp only [defectA, T, F]
    _ ≤ (8^2 * 200) * 1 * (wMass t - 1/mi) := by
        apply mul_le_mul_of_nonneg_right _ hd0
        exact mul_le_mul_of_nonneg_left hc1 (by norm_num)
    _ ≤ (8^2 * 200) * 1 * (1/168) :=
        mul_le_mul_of_nonneg_left hd1 (by norm_num)
    _ = 1600/21 := by norm_num

/-- The geometric-series tail identity, as a rational identity. -/
theorem tail_identity {x : ℝ} (hx : x ≠ 1) :
    1/(1-x) - ∑ k ∈ Finset.range 6, x^k = x^6/(1-x) := by
  rw [geom_sum_eq hx 6]
  have h1 : x - 1 = -(1 - x) := by ring
  rw [h1, div_neg, sub_neg_eq_add, ← add_div]
  congr 1
  ring

/-- Geometric tail: the exact residual of the degree-five truncation. -/
theorem wMass_sub_trunc (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    wMass t - wTrunc5 t = (1/mi) * ((t/15)^6 / (1 - t/15)) := by
  have hx1 : (t/15 : ℝ) ≠ 1 := by have h := ht.2; linarith
  have hm : mass t = 12 * (1 - t/15) := by
    simp only [mass, mi, sT, tc_eq t ht]; ring
  have h1 : (1:ℝ)/(12*(1-t/15)) = (1/mi) * (1/(1 - t/15)) := by
    simp only [mi]; rw [div_mul_div_comm]; simp
  rw [wMass, hm, h1]
  simp only [wTrunc5, mi]
  rw [← mul_sub, tail_identity hx1]

/-- The truncated variable-mass defect bound: 64/637875 = 1.01e-4 m. -/
theorem defectB_bound {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36))
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : |defectB θ t| ≤ 64/637875 := by
  obtain ⟨hc0, hc1⟩ := cos_bounds hθ
  have hx0 : (0:ℝ) ≤ t/15 := by have h := ht.1; linarith
  have hx1 : t/15 ≤ 1/15 := by have h := ht.2; linarith
  have hden : (0:ℝ) ≤ 1 - t/15 := by have h := ht.2; linarith
  have ht0 : (0:ℝ) ≤ (t/15)^6 / (1 - t/15) := div_nonneg (pow_nonneg hx0 6) hden
  have hpow : (t/15)^6 ≤ (1/15)^6 := pow_le_pow_left₀ hx0 hx1 6
  have hden' : (14/15 : ℝ) ≤ 1 - t/15 := by have h := ht.2; linarith
  have htail : (t/15)^6 / (1 - t/15) ≤ (1/15)^6 / (14/15) :=
    div_le_div₀ (by positivity) hpow (by norm_num) hden'
  have hnn : (0:ℝ) ≤ defectB θ t := by
    rw [defectB, wMass_sub_trunc t ht]
    simp only [T, F, mi]
    exact mul_nonneg (mul_nonneg (by norm_num) hc0)
      (mul_nonneg (by norm_num) ht0)
  rw [abs_of_nonneg hnn, defectB, wMass_sub_trunc t ht]
  simp only [T, F, mi]
  calc (8:ℝ)^2 * 200 * Real.cos θ * (1/12 * ((t/15)^6 / (1 - t/15)))
      = ((8^2 * 200) * Real.cos θ) * (1/12 * ((t/15)^6 / (1 - t/15))) := by ring
    _ ≤ ((8^2 * 200) * 1) * (1/12 * ((1/15)^6 / (14/15))) := by
        apply mul_le_mul _ _ (mul_nonneg (by norm_num) ht0) (by norm_num)
        · exact mul_le_mul_of_nonneg_left hc1 (by norm_num)
        · exact mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = 64/637875 := by norm_num

/-- The frozen-mass predictor, certified by the zero-curvature certificate. -/
theorem frozen_mass_certificate {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36)) (t : ℝ) (ht : t ∈ Icc 0 1) :
    |errA θ t| ≤ (1600/21) * value 0 t ∧
      |velA θ t| ≤ (1600/21) * velocity 0 t := by
  have h := ConstantSecondOrderBound.response (errA θ) (velA θ) (defectA θ)
    (κ := 0) (F := 1600/21) le_rfl (by norm_num) (by norm_num)
    (antiderivative_continuous (antiderivative_continuous (defectA_continuous θ)))
    (antiderivative_continuous (defectA_continuous θ))
    (fun s _ => errA_hasDeriv θ s) (fun s _ => velA_hasDeriv θ s)
    (errA_zero θ) (velA_zero θ) (by
      intro s hs
      simpa [Real.norm_eq_abs] using defectA_bound hθ s hs)
  simpa [Real.norm_eq_abs] using h t ht

/-- The variable-mass predictor, certified by the zero-curvature certificate. -/
theorem variable_mass_certificate {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36)) (t : ℝ) (ht : t ∈ Icc 0 1) :
    |errB θ t| ≤ (64/637875) * value 0 t ∧
      |velB θ t| ≤ (64/637875) * velocity 0 t := by
  have h := ConstantSecondOrderBound.response (errB θ) (velB θ) (defectB θ)
    (κ := 0) (F := 64/637875) le_rfl (by norm_num) (by norm_num)
    (antiderivative_continuous (antiderivative_continuous (defectB_continuous θ)))
    (antiderivative_continuous (defectB_continuous θ))
    (fun s _ => errB_hasDeriv θ s) (fun s _ => velB_hasDeriv θ s)
    (errB_zero θ) (velB_zero θ) (by
      intro s hs
      simpa [Real.norm_eq_abs] using defectB_bound hθ s hs)
  simpa [Real.norm_eq_abs] using h t ht

theorem value_zero_one : value 0 1 = 1/2 := by
  simp [value, polynomial]

theorem velocity_zero_one : velocity 0 1 = 1 := by
  simp [velocity, polynomial]
  norm_num

/-- Endpoint certificate for the frozen-mass predictor: 38.10 m, 9.524 m/s. -/
theorem frozen_mass_endpoint {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36)) :
    |errA θ 1| ≤ 381/10 ∧ (1/T) * |velA θ 1| ≤ 2381/250 := by
  have h := frozen_mass_certificate hθ 1 ⟨by norm_num, le_rfl⟩
  rw [value_zero_one, velocity_zero_one] at h
  constructor
  · exact h.1.trans (by norm_num)
  · have h2 : (1/T) * |velA θ 1| ≤ (1/8) * ((1600/21) * 1) := by
      rw [T]; gcongr; exact h.2
    exact h2.trans (by norm_num)

/-- Endpoint certificate for the variable-mass predictor:
5.02e-5 m and 1.26e-5 m/s. -/
theorem variable_mass_endpoint {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36)) :
    |errB θ 1| ≤ 502/10^7 ∧ (1/T) * |velB θ 1| ≤ 126/10^7 := by
  have h := variable_mass_certificate hθ 1 ⟨by norm_num, le_rfl⟩
  rw [value_zero_one, velocity_zero_one] at h
  constructor
  · exact h.1.trans (by norm_num)
  · have h2 : (1/T) * |velB θ 1| ≤ (1/8) * ((64/637875) * 1) := by
      rw [T]; gcongr; exact h.2
    exact h2.trans (by norm_num)

end GNC.DroneCertificate
