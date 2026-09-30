import GNC.Preintegration.CenteredFohBounds
import GNC.Analysis.CenteredFohWeights
import GNC.Analysis.DysonWeightedTranslation

/-! Physical FOH remainders with exact time weights. The finite propagators
are unchanged. The improvement comes only from integrating the pointwise
rotation remainder instead of its worst endpoint value.
-/
noncomputable section
open Set Matrix NormedSpace
namespace GNC.Preintegration.CenteredFoh

theorem errorFlow_prefix_bound (R : ℝ → SO3) (F G : Vec3)
    (hR : ∀ t, HasDerivAt (fun s => rotation (R s))
      (rotation (R t) * (hat F + (t-1/2) • hat G)) t) (hR₀ : R 0 = 1)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖errorFlow R F t - Dyson.approx (residual F G) n t‖ ≤
      ((enorm G/4)^n / (n.factorial : ℝ)) * Dyson.centeredMass t^n := by
  have hd (s : ℝ) : HasDerivAt (fun x => (enorm G/4)*Dyson.centeredMass x)
      (|s-1/2| * enorm G) s := by
    convert (Dyson.centeredMass_derivative s).const_mul (enorm G/4) using 1
    ring
  have hh := Dyson.approx_error_bound_majorant (residual F G) (errorFlow R F)
    (fun s => |s-1/2| * enorm G) (fun s => (enorm G/4)*Dyson.centeredMass s)
    (residual_continuous F G) (by fun_prop) (errorFlow_derivative R F G hR)
    (errorFlow_initial R F hR₀) hd (by simp [Dyson.centeredMass_zero])
    (T := 1) (M := 1) (by norm_num) (by norm_num)
    (fun s _ => residual_norm_le F G s)
    (fun s hs => mul_nonneg (div_nonneg (enorm_nonneg G) (by norm_num))
      (Dyson.centeredMass_nonneg hs.1))
    (fun s _ => errorFlow_norm_le R F s) n t ht
  apply hh.trans_eq
  rw [mul_pow]
  ring

/-- Same physical approximations as `balanced_foh_remainder`; only the
translation bounds are sharpened. `N+3` is the first omitted residual order.
No hypotheses about the unknown error or numerical tolerances are added. -/
theorem balanced_weighted_physical_remainder
    (R : ℝ → SO3) (v p : ℝ → E3) (F G : Vec3) {T : ℝ} (hT : 0 ≤ T)
    (a₀ a₁ : E3)
    (hR : ∀ t, HasDerivAt (fun s => rotation (R s))
      (rotation (R t) * (hat F + (t-1/2) • hat G)) t) (hR₀ : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotation (R t) (acceleration T a₀ a₁ t)) t) (hv₀ : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (T • v t) t) (hp₀ : p 0 = 0) (N : ℕ) :
    ‖v 1 - predictVelocity F G T a₀ a₁ (N+1)‖ ≤
      ((enorm G/4)^(N+3) / ((N+3).factorial : ℝ)) * T *
        Dyson.velocityWeight (N+3) ‖a₀‖ ‖a₁‖ ∧
    ‖p 1 - predictPosition F G T a₀ a₁ (N+2)‖ ≤
      ((enorm G/4)^(N+3) / ((N+3).factorial : ℝ)) * T^2 *
        Dyson.positionWeight (N+3) ‖a₀‖ ‖a₁‖ := by
  let δ := (enorm G/4)^(N+3) / ((N+3).factorial : ℝ)
  have hvc (t : ℝ) : HasDerivAt (fun s => column (v s))
      (errorFlow R F t * columnInput F T a₀ a₁ t) t := by
    have hh := column.hasFDerivAt.comp_hasDerivAt t (hv t)
    convert hh using 1
    rw [columnInput, column_mul, transported, ← ContinuousLinearMap.mul_apply, errorFlow_mean]
  have hpc (t : ℝ) : HasDerivAt (fun s => column (p s)) (T • column (v t)) t := by
    simpa only [map_smul] using column.hasFDerivAt.comp_hasDerivAt t (hp t)
  have hrc : Continuous (errorFlow R F) := continuous_iff_continuousAt.mpr
    (fun t => (errorFlow_derivative R F G hR t).continuousAt)
  obtain ⟨hvbound, hpbound⟩ := Dyson.translation_weighted_bound
    (residual F G) (errorFlow R F) (columnInput F T a₀ a₁)
    (fun t => column (v t)) (fun t => column (p t))
    (fun t => δ * Dyson.centeredMass t^(N+3))
    (fun t => T*((1-t)*‖a₀‖+t*‖a₁‖))
    (residual_continuous F G) hrc (columnInput_continuous F T a₀ a₁)
    (by fun_prop) (by fun_prop) hvc (by simp [hv₀]) hT
    (S := 1) (by norm_num) hpc (by simp [hp₀]) (N+3)
    (fun t ht => errorFlow_prefix_bound R F G hR hR₀ (N+3) ht)
    (fun t ht => by
      rw [columnInput, column_norm, transported, mean_rotation, rotation_norm_apply]
      exact acceleration_norm_le hT a₀ a₁ ht)
  have hvweight : (∫ t in (0 : ℝ)..1,
      (δ * Dyson.centeredMass t^(N+3)) * (T*((1-t)*‖a₀‖+t*‖a₁‖))) =
        δ*T*Dyson.velocityWeight (N+3) ‖a₀‖ ‖a₁‖ := by
    rw [Dyson.velocityWeight, ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  have hpweight : T * (∫ t in (0 : ℝ)..1,
      (1-t)*((δ * Dyson.centeredMass t^(N+3)) * (T*((1-t)*‖a₀‖+t*‖a₁‖)))) =
        δ*T^2*Dyson.positionWeight (N+3) ‖a₀‖ ‖a₁‖ := by
    calc
      _ = T*(δ*T*Dyson.positionWeight (N+3) ‖a₀‖ ‖a₁‖) := by
        congr 1
        rw [Dyson.positionWeight, ← intervalIntegral.integral_const_mul]
        congr 1
        funext t
        ring
      _ = _ := by ring
  rw [hvweight] at hvbound
  rw [hpweight] at hpbound
  constructor
  · have hh := (column (v 1) - Dyson.velocityApprox (residual F G)
        (columnInput F T a₀ a₁) (N+3) 1).le_opNorm anchor
    rw [anchor_norm, mul_one] at hh
    have he := velocity_column_evaluation (residual F G) (transported F T a₀ a₁)
      (residual_continuous F G) (transported_continuous F T a₀ a₁) (N+3) 1
    rw [ContinuousLinearMap.sub_apply, column_anchor] at hh
    change Dyson.velocityApprox (residual F G) (columnInput F T a₀ a₁) (N+3) 1 anchor =
      predictVelocity F G T a₀ a₁ (N+1) at he
    rw [he] at hh
    exact hh.trans hvbound
  · have hh := (column (p 1) - T • Dyson.positionApprox (residual F G)
        (columnInput F T a₀ a₁) ((N+3)+1) 1).le_opNorm anchor
    rw [anchor_norm, mul_one] at hh
    have he := position_column_evaluation (residual F G) (transported F T a₀ a₁)
      (residual_continuous F G) (transported_continuous F T a₀ a₁) (N+3) 1
    have he' : (T • Dyson.positionApprox (residual F G)
        (columnInput F T a₀ a₁) ((N+3)+1) 1) anchor =
          predictPosition F G T a₀ a₁ (N+2) := by
      change T • (Dyson.positionApprox (residual F G)
        (fun t => column (transported F T a₀ a₁ t)) ((N+3)+1) 1 anchor) = _
      rw [he]
      rfl
    rw [ContinuousLinearMap.sub_apply, column_anchor, he'] at hh
    exact hh.trans hpbound

/-- Sample-based weighted theorem, including the unchanged attitude bound. -/
theorem balanced_weighted_foh_remainder
    (R : ℝ → SO3) (v p : ℝ → E3) {T : ℝ} (hT : 0 ≤ T)
    (ω₀ ω₁ : Vec3) (a₀ a₁ : E3)
    (hR : ∀ t, HasDerivAt (fun s => rotation (R s))
      (rotation (R t) * hat (T • ((1-t) • ω₀ + t • ω₁))) t) (hR₀ : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotation (R t) (acceleration T a₀ a₁ t)) t) (hv₀ : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (T • v t) t) (hp₀ : p 0 = 0) (N : ℕ) :
    ‖rotation (R 1) - predictRotation (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) N‖ ≤
      (T*enorm (ω₁-ω₀)/4)^(N+3) / ((N+3).factorial : ℝ) ∧
    ‖v 1 - predictVelocity (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) T a₀ a₁ (N+1)‖ ≤
      ((T*enorm (ω₁-ω₀)/4)^(N+3) / ((N+3).factorial : ℝ)) * T *
        Dyson.velocityWeight (N+3) ‖a₀‖ ‖a₁‖ ∧
    ‖p 1 - predictPosition (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) T a₀ a₁ (N+2)‖ ≤
      ((T*enorm (ω₁-ω₀)/4)^(N+3) / ((N+3).factorial : ℝ)) * T^2 *
        Dyson.positionWeight (N+3) ‖a₀‖ ‖a₁‖ := by
  refine ⟨(foh_remainder R v p hT ω₀ ω₁ a₀ a₁ hR hR₀ hv hv₀ hp hp₀ N).1, ?_⟩
  have h := balanced_weighted_physical_remainder R v p
    (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) hT a₀ a₁
    (fun t => by simpa only [sampled_generator] using hR t) hR₀ hv hv₀ hp hp₀ N
  simpa only [slopeAngle, enorm_smul, abs_of_nonneg hT] using h

/-- Closed rational weights for the implemented common correction order two.
The integers 29, 99, 257 and 352 come from exact polynomial integration of
the centered slope envelope, as proved in `CenteredFohWeights`. -/
theorem balanced_order_two_weighted_remainder
    (R : ℝ → SO3) (v p : ℝ → E3) {T : ℝ} (hT : 0 ≤ T)
    (ω₀ ω₁ : Vec3) (a₀ a₁ : E3)
    (hR : ∀ t, HasDerivAt (fun s => rotation (R s))
      (rotation (R t) * hat (T • ((1-t) • ω₀ + t • ω₁))) t) (hR₀ : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotation (R t) (acceleration T a₀ a₁ t)) t) (hv₀ : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (T • v t) t) (hp₀ : p 0 = 0) :
    ‖rotation (R 1) - predictRotation (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) 0‖ ≤
      (T*enorm (ω₁-ω₀)/4)^3 / 6 ∧
    ‖v 1 - predictVelocity (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) T a₀ a₁ 1‖ ≤
      ((T*enorm (ω₁-ω₀)/4)^3 / 6) * T * ((29*‖a₀‖+99*‖a₁‖)/640) ∧
    ‖p 1 - predictPosition (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) T a₀ a₁ 2‖ ≤
      ((T*enorm (ω₁-ω₀)/4)^3 / 6) * T^2 * ((257*‖a₀‖+352*‖a₁‖)/13440) := by
  simpa [Dyson.velocityWeight_three, Dyson.positionWeight_three, Nat.factorial] using
    balanced_weighted_foh_remainder R v p hT ω₀ ω₁ a₀ a₁ hR hR₀ hv hv₀ hp hp₀ 0

/-- Entire weighted remainder plus exact distances to the reported output.
Numerical certification must bound these evaluation distances separately. -/
theorem balanced_weighted_reported_remainder
    (R : ℝ → SO3) (v p : ℝ → E3) {T : ℝ} (hT : 0 ≤ T)
    (ω₀ ω₁ : Vec3) (a₀ a₁ : E3)
    (hR : ∀ t, HasDerivAt (fun s => rotation (R s))
      (rotation (R t) * hat (T • ((1-t) • ω₀ + t • ω₁))) t) (hR₀ : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotation (R t) (acceleration T a₀ a₁ t)) t) (hv₀ : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (T • v t) t) (hp₀ : p 0 = 0) (N : ℕ)
    (Rhat : SO3) (vhat phat : E3) :
    ‖rotation (R 1) - rotation Rhat‖ ≤
      (T*enorm (ω₁-ω₀)/4)^(N+3) / ((N+3).factorial : ℝ) +
      ‖predictRotation (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) N - rotation Rhat‖ ∧
    ‖v 1 - vhat‖ ≤
      ((T*enorm (ω₁-ω₀)/4)^(N+3) / ((N+3).factorial : ℝ)) * T *
        Dyson.velocityWeight (N+3) ‖a₀‖ ‖a₁‖ +
      ‖predictVelocity (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) T a₀ a₁ (N+1) - vhat‖ ∧
    ‖p 1 - phat‖ ≤
      ((T*enorm (ω₁-ω₀)/4)^(N+3) / ((N+3).factorial : ℝ)) * T^2 *
        Dyson.positionWeight (N+3) ‖a₀‖ ‖a₁‖ +
      ‖predictPosition (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) T a₀ a₁ (N+2) - phat‖ := by
  have h := balanced_weighted_foh_remainder R v p hT ω₀ ω₁ a₀ a₁ hR hR₀ hv hv₀ hp hp₀ N
  refine ⟨?_, ?_, ?_⟩
  · exact (norm_sub_le_norm_sub_add_norm_sub _
      (predictRotation (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) N) _).trans
      (_root_.add_le_add h.1 le_rfl)
  · exact (norm_sub_le_norm_sub_add_norm_sub _
      (predictVelocity (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) T a₀ a₁ (N+1)) _).trans
      (_root_.add_le_add h.2.1 le_rfl)
  · exact (norm_sub_le_norm_sub_add_norm_sub _
      (predictPosition (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) T a₀ a₁ (N+2)) _).trans
      (_root_.add_le_add h.2.2 le_rfl)

end GNC.Preintegration.CenteredFoh
