import GNC.Applications.OrbitalComparison.LieRadiusData.Budget

/-! Uniform physical bounds for the direct Lie-coordinate candidate. Every
range is derived from a kernel-checked polynomial record, including reference
phase and scalar radius reconstruction errors. -/
noncomputable section
namespace GNC.OrbitalComparison.LieRadiusData
open LieRadiusPolynomial ParameterPolynomial Set SpatialBurn Matrix

theorem scalar_norm_bound (p : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    |value p x t| ≤ ‖DiskPolynomial.vectorValue ![p] x t‖ := by
  simpa [DiskPolynomial.vectorValue,Real.norm_eq_abs] using
    PiLp.norm_apply_le (DiskPolynomial.vectorValue ![p] x t) (0 : Fin 1)

theorem z_physical_bound {θ t : ℝ} (hθ : |θ| ≤ (sigma:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (LieSTTOutput.value3 input.z ![θ,0,0] t) ≤ (Zmax:ℝ)*t^2 := by
  have h := z_quadratic (by simpa only [sigma,Rat.cast_div,Rat.cast_ofNat] using hθ) ht
  have he := PolynomialOrder.value_at_rational (z.bound 0) 1
  norm_num only [Rat.cast_one] at he
  rw [he] at h
  simpa only [Zmax,mul_comm] using h

theorem h_physical_bound {θ t : ℝ} (hθ : |θ| ≤ (sigma:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) :
    |value input.h ![θ,0,0] t| ≤ (Hmax:ℝ)*t^2 := by
  have hb := (scalar_norm_bound input.h ![θ,0,0] t).trans
    (h_quadratic (by simpa only [sigma,Rat.cast_div,Rat.cast_ofNat] using hθ) ht)
  have he := PolynomialOrder.value_at_rational (h.bound 0) 1
  norm_num only [Rat.cast_one] at he
  rw [he] at hb
  simpa only [Hmax,mul_comm] using hb

theorem u_physical_bound {θ t : ℝ} (hθ : |θ| ≤ (sigma:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) :
    |value input.radiusDeviation ![θ,0,0] t| ≤ (Umax:ℝ)*t^2 := by
  have hb := (scalar_norm_bound input.radiusDeviation ![θ,0,0] t).trans
    (u_quadratic (by simpa only [sigma,Rat.cast_div,Rat.cast_ofNat] using hθ) ht)
  have he := PolynomialOrder.value_at_rational (u.bound 0) 1
  norm_num only [Rat.cast_one] at he
  rw [he] at hb
  simpa only [Umax,mul_comm] using hb

theorem constraint_physical_bound {θ t : ℝ} (hθ : |θ| ≤ (sigma:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) :
    |value input.constraintLinear ![θ,0,0] t| ≤
      PolynomialOrder.value (constraint_linear.bound 0) t :=
  (scalar_norm_bound input.constraintLinear ![θ,0,0] t).trans
    (constraint_linear_bound (by simpa only [sigma,Rat.cast_div,Rat.cast_ofNat] using hθ) ht.1)

theorem real_checks : 0 ≤ (input.μ:ℝ) ∧ 0 < (input.r:ℝ) ∧ 0 ≤ (sigma:ℝ) ∧
    0 ≤ (Zmax:ℝ) ∧ 0 ≤ (Hmax:ℝ) ∧ (Hmax:ℝ)<1 ∧ 0 ≤ (Umax:ℝ) ∧ 0 ≤ (delta:ℝ) ∧
    0 ≤ (Ctheta:ℝ) ∧ 0 ≤ (Htheta:ℝ) ∧ 0 ≤ (forceBound:ℝ) ∧ 0 ≤ (radiusError:ℝ) ∧
    0 < (regionRadius:ℝ) ∧ 2*(regionRadius:ℝ) < (input.r:ℝ) := by
  exact_mod_cast basic_checks

theorem radius_physical_bound {θ t : ℝ} (hθ : |θ| ≤ (sigma:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) :
    |(‖input.position θ t‖^2/(input.r:ℝ)^2-1)-value input.radiusDeviation ![θ,0,0] t| ≤
      (radiusError:ℝ)*t^2 := by
  obtain ⟨hμ,hr,hσ,hZ,hH,hH1,hU,hδ,hC,hS,hB,hE,hP,hPr⟩ := real_checks
  have hz := z_physical_bound hθ ht
  have ht2 : t^2 ≤ 1 := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have ht4 : (t^2)^2 ≤ t^2 := by nlinarith [sq_nonneg t]
  have he := input.radius_error_bound hr θ t (axis_bound ht) (cosine_bound hθ ht) (sine_bound hθ ht)
  have htr : LieRadiusApproximation.translationBudget |θ| (delta:ℝ) Ctheta Htheta ≤ (translationTail:ℝ) := by
    simp only [translationTail,LieRadiusApproximation.translationBudget,
      Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat]
    gcongr
  have hgr : LieRadiusApproximation.gramBudget |θ| (delta:ℝ) Ctheta ≤ (gramTail:ℝ) := by
    simp only [gramTail,LieRadiusApproximation.gramBudget,
      Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat]
    gcongr
  have htr0 : 0 ≤ (translationTail:ℝ) := by
    simp only [translationTail,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat]
    positivity
  have hgr0 : 0 ≤ (gramTail:ℝ) := by
    simp only [gramTail,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat]
    positivity
  have hz2 : enorm (LieSTTOutput.value3 input.z ![θ,0,0] t)^2 ≤ (Zmax:ℝ)^2*t^2 := by
    calc
      _ ≤ ((Zmax:ℝ)*t^2)^2 := pow_le_pow_left₀ (enorm_nonneg _) hz 2
      _ = (Zmax:ℝ)^2*(t^2)^2 := by ring
      _ ≤ (Zmax:ℝ)^2*t^2 := mul_le_mul_of_nonneg_left ht4 (sq_nonneg _)
  apply he.trans
  calc
    _ ≤ (2/(input.r:ℝ))*(translationTail:ℝ)*((Zmax:ℝ)*t^2)+
        ((gramTail:ℝ)/(input.r:ℝ)^2)*((Zmax:ℝ)^2*t^2) := by
          gcongr
          exact enorm_nonneg _
    _ = _ := by
      simp only [radiusError,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat]
      ring

theorem translation_bound {θ t : ℝ} (hθ : |θ| ≤ (sigma:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) : ‖input.translation θ t‖ ≤ (regionRadius:ℝ) := by
  obtain ⟨hμ,hr,hσ,hZ,hH,hH1,hU,hδ,hC,hS,hB,hE,hP,hPr⟩ := real_checks
  have ht2 : t^2 ≤ 1 := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  change enorm (input.translation θ t).ofLp ≤ _
  rw [input.translation_value3,rho_value,enorm_smul]
  calc
    _ ≤ (sigma:ℝ)*((Zmax:ℝ)*t^2) :=
      mul_le_mul hθ (z_physical_bound hθ ht) (enorm_nonneg _) hσ
    _ ≤ (sigma:ℝ)*(Zmax:ℝ) := by
      nlinarith [mul_nonneg hσ (mul_nonneg hZ (sub_nonneg.mpr ht2))]
    _ = _ := by simp only [regionRadius,Rat.cast_mul]

theorem chart_bound {θ : ℝ} (hθ : |θ| ≤ (sigma:ℝ)) : |θ| < 2*Real.pi := by
  have hs : (sigma:ℝ) < 2*Real.pi := by
    norm_num only [sigma,Rat.cast_div,Rat.cast_ofNat]
    linarith [Real.two_le_pi]
  exact hθ.trans_lt hs

/-- Full inverse-square ODE defect for all pointing angles and all burn
times. This bound is independent of a Cartesian polynomial trajectory. -/
theorem physical_defect {θ t : ℝ} (hθ : |θ| ≤ (sigma:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) :
    ‖input.acceleration θ t-input.model.acceleration θ t (input.position θ t)‖ ≤
      PolynomialOrder.value rawForcing t := by
  obtain ⟨hμ,hr,hσ,hZ,hH,hH1,hU,hδ,hC,hS,hB,hE,hP,hPr⟩ := real_checks
  have ht2 : t^2 ≤ 1 := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have hht : (Hmax:ℝ)*t^2 < 1 := lt_of_le_of_lt (by nlinarith) hH1
  have hcp := PolynomialOrder.value_nonnegative _ constraint_nonnegative ht.1
  have hR : enorm (LieSTTOutput.value3 input.residual ![θ,0,0] t) ≤
      PolynomialOrder.value (lie_residual.bound 0) t :=
    lie_residual_bound (by simpa only [sigma,Rat.cast_div,Rat.cast_ofNat] using hθ) ht.1
  have hd := input.direct_defect hμ hr θ t (chart_bound hθ) (axis_bound ht)
    (translation_bound hθ ht) (by linarith) (h_physical_bound hθ ht) hht
    (force_bound ht) (u_physical_bound hθ ht) (radius_physical_bound hθ ht)
    (constraint_physical_bound hθ ht) hR
  rw [rawForcing_value]
  apply hd.trans
  apply (LieRadiusTimeBound.angle_budget_mono hμ hr hδ hP.le
    (mul_nonneg hH (sq_nonneg t)) hB hθ).trans
  exact LieRadiusTimeBound.budget_le_forcing hμ hr hσ hP.le hH hU hE hcp ht

end GNC.OrbitalComparison.LieRadiusData
