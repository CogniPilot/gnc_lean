import GNC.Analysis.DysonTranslation
import GNC.Lie.RotationDifferential
import GNC.Lie.Exponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Physical SO(3)/Euclidean specialization of the centered FOH remainder.
Operators act on genuine Euclidean 3-space, not the entrywise matrix norm.
Translation columns are embedded isometrically as rank-one operators so that
the existing triangular actual-flow theorem can be reused unchanged.
-/
noncomputable section
open Set Matrix NormedSpace
open scoped Matrix.Norms.Operator
namespace GNC.Preintegration.CenteredFoh

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev Op := E3 →L[ℝ] E3
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
local instance : NormedAlgebra ℚ Op := NormedAlgebra.restrictScalars ℚ ℝ Op

def matrixOp : Mat3 ≃⋆ₐ[ℝ] Op := Matrix.toEuclideanCLM
def rotation (R : SO3) : Op := matrixOp R.val
def hat (q : Vec3) : Op := matrixOp (skew q)
def mean (F : Vec3) (t : ℝ) : Op := exp (t • hat F)
def unmean (F : Vec3) (t : ℝ) : Op := exp (t • (-(hat F)))
def residual (F G : Vec3) (t : ℝ) : Op :=
  mean F t * ((t-1/2) • hat G) * unmean F t
def anchor : E3 := EuclideanSpace.single 0 1
def column : E3 →L[ℝ] Op :=
  ContinuousLinearMap.smulRightL ℝ E3 E3 (innerSL ℝ anchor)

theorem matrixOp_continuous : Continuous (matrixOp : Mat3 → Op) :=
  matrixOp.toAlgEquiv.toLinearMap.toContinuousLinearMap.continuous

theorem rotation_norm_apply (R : SO3) (x : E3) : ‖rotation R x‖ = ‖x‖ := by
  exact rotate_enorm R (WithLp.ofLp x)

theorem rotation_norm_le (R : SO3) : ‖rotation R‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp only [rotation_norm_apply, one_mul, le_refl]

theorem hat_norm_le (q : Vec3) : ‖hat q‖ ≤ enorm q := by
  apply ContinuousLinearMap.opNorm_le_bound _ (enorm_nonneg q)
  intro x
  change enorm (skew q *ᵥ WithLp.ofLp x) ≤ _
  rw [skew_mulVec]
  exact cross_enorm_le q (WithLp.ofLp x)

theorem mean_rotation (F : Vec3) (t : ℝ) :
    mean F t = rotation (rotationExp (t • F)) := by
  unfold mean rotation rotationExp hat
  change exp (t • matrixOp (skew F)) = matrixOp (exp (skew (t • F)))
  rw [skew_smul, NormedSpace.map_exp matrixOp matrixOp_continuous, map_smul]

theorem mean_norm_le (F : Vec3) (t : ℝ) : ‖mean F t‖ ≤ 1 := by
  rw [mean_rotation]
  exact rotation_norm_le _

theorem unmean_eq (F : Vec3) (t : ℝ) : unmean F t = mean F (-t) := by
  unfold unmean mean
  congr 1
  module

theorem unmean_norm_le (F : Vec3) (t : ℝ) : ‖unmean F t‖ ≤ 1 := by
  rw [unmean_eq]
  exact mean_norm_le _ _

theorem unmean_mean (F : Vec3) (t : ℝ) : unmean F t * mean F t = 1 := by
  simpa [unmean, mean] using MixedInvariant.exp_cancel' (t • hat F)

theorem mean_unmean (F : Vec3) (t : ℝ) : mean F t * unmean F t = 1 := by
  simpa [unmean, mean] using MixedInvariant.exp_cancel (t • hat F)

theorem mean_continuous (F : Vec3) : Continuous (mean F) := by
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

theorem unmean_continuous (F : Vec3) : Continuous (unmean F) := by
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

theorem residual_continuous (F G : Vec3) : Continuous (residual F G) :=
  ((mean_continuous F).mul ((continuous_id.sub continuous_const).smul continuous_const)).mul
    (unmean_continuous F)

theorem residual_norm_le (F G : Vec3) (t : ℝ) :
    ‖residual F G t‖ ≤ |t-1/2| * enorm G := by
  have hG := enorm_nonneg G
  have hc : ‖(t-1/2) • hat G‖ ≤ |t-1/2| * enorm G := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hat_norm_le G) (abs_nonneg _)
  calc
    _ ≤ ‖mean F t‖ * ‖(t-1/2) • hat G‖ * ‖unmean F t‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * (|t-1/2| * enorm G) * 1 := by
      gcongr <;> first | positivity | exact mean_norm_le F t | exact hc | exact unmean_norm_le F t
    _ = _ := by ring

theorem anchor_norm : ‖anchor‖ = 1 := by simp [anchor]

theorem rotation_norm (R : SO3) : ‖rotation R‖ = 1 := by
  apply le_antisymm (rotation_norm_le R)
  have hh := (rotation R).le_opNorm anchor
  simpa only [rotation_norm_apply, anchor_norm, mul_one] using hh

theorem column_apply (x y : E3) : column x y = inner ℝ anchor y • x := rfl

theorem column_norm (x : E3) : ‖column x‖ = ‖x‖ := by
  change ‖InnerProductSpace.rankOne ℝ x anchor‖ = ‖x‖
  simp [anchor_norm]

theorem column_anchor (x : E3) : column x anchor = x := by
  simp [column_apply, anchor_norm]

theorem column_mul (A : Op) (x : E3) : A * column x = column (A x) := by
  ext y
  simp [ContinuousLinearMap.mul_apply, column_apply]

def acceleration (T : ℝ) (a₀ a₁ : E3) (t : ℝ) : E3 :=
  T • ((1-t) • a₀ + t • a₁)
def transported (F : Vec3) (T : ℝ) (a₀ a₁ : E3) (t : ℝ) : E3 :=
  mean F t (acceleration T a₀ a₁ t)
def columnInput (F : Vec3) (T : ℝ) (a₀ a₁ : E3) (t : ℝ) : Op :=
  column (transported F T a₀ a₁ t)
def errorFlow (R : ℝ → SO3) (F : Vec3) (t : ℝ) : Op :=
  rotation (R t) * unmean F t

/-- The input slope is known exactly under the FOH model. -/
theorem acceleration_derivative (T : ℝ) (a₀ a₁ : E3) (t : ℝ) :
    HasDerivAt (acceleration T a₀ a₁) (T • (a₁-a₀)) t := by
  have hh := ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const a₀).add
    ((hasDerivAt_id t).smul_const a₁)).const_smul T
  convert hh using 1
  simp [sub_eq_add_neg, add_comm]

/-- Removing mean rotation from the rotation ODE does not make the transformed
acceleration slowly varying: its derivative still contains the mean generator.
This explains why quadrature in the transformed frame can still resolve F. -/
theorem transported_derivative (F : Vec3) (T : ℝ) (a₀ a₁ : E3) (t : ℝ) :
    HasDerivAt (transported F T a₀ a₁)
      (hat F (transported F T a₀ a₁ t) + mean F t (T • (a₁-a₀))) t := by
  have hh := (hasDerivAt_exp_smul_const' (hat F) t).clm_apply
    (acceleration_derivative T a₀ a₁ t)
  simpa only [transported, mean, ContinuousLinearMap.mul_apply] using hh

theorem transported_continuous (F : Vec3) (T : ℝ) (a₀ a₁ : E3) :
    Continuous (transported F T a₀ a₁) := by
  exact (mean_continuous F).clm_apply (by unfold acceleration; fun_prop)

theorem columnInput_continuous (F : Vec3) (T : ℝ) (a₀ a₁ : E3) :
    Continuous (columnInput F T a₀ a₁) :=
  column.continuous.comp (transported_continuous F T a₀ a₁)

theorem acceleration_norm_le {T : ℝ} (hT : 0 ≤ T) (a₀ a₁ : E3)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖acceleration T a₀ a₁ t‖ ≤ T * ((1-t)*‖a₀‖ + t*‖a₁‖) := by
  unfold acceleration
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT]
  apply mul_le_mul_of_nonneg_left _ hT
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
    abs_of_nonneg (sub_nonneg.mpr ht.2)] using norm_add_le ((1-t) • a₀) (t • a₁)

theorem impulse_bound (F : Vec3) {T : ℝ} (hT : 0 ≤ T) (a₀ a₁ : E3) :
    (∫ t in (0 : ℝ)..1, ‖columnInput F T a₀ a₁ t‖) ≤ T*(‖a₀‖+‖a₁‖)/2 := by
  have he (t : ℝ) : ‖columnInput F T a₀ a₁ t‖ = ‖acceleration T a₀ a₁ t‖ := by
    rw [columnInput, column_norm, transported, mean_rotation, rotation_norm_apply]
  have hi : (∫ t in (0 : ℝ)..1, ‖columnInput F T a₀ a₁ t‖) ≤
      ∫ t in (0 : ℝ)..1, T*((1-t)*‖a₀‖+t*‖a₁‖) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((columnInput_continuous F T a₀ a₁).norm.intervalIntegrable 0 1)
      ((by fun_prop : Continuous (fun t : ℝ => T*((1-t)*‖a₀‖+t*‖a₁‖))).intervalIntegrable 0 1)
    intro t ht
    rw [he]
    exact acceleration_norm_le hT a₀ a₁ ht
  apply hi.trans_eq
  have hf : (fun t : ℝ => T*((1-t)*‖a₀‖+t*‖a₁‖)) =
      (fun t : ℝ => T*‖a₀‖+t*(T*(‖a₁‖-‖a₀‖))) := by
    funext t; ring
  rw [hf, intervalIntegral.integral_add
    (f := fun _ : ℝ => T*‖a₀‖) (g := fun t : ℝ => t*(T*(‖a₁‖-‖a₀‖))) intervalIntegrable_const
    ((by fun_prop : Continuous (fun t : ℝ => t*(T*(‖a₁‖-‖a₀‖)))).intervalIntegrable _ _),
    intervalIntegral.integral_mul_const]
  norm_num [integral_id]
  ring

theorem errorFlow_norm_le (R : ℝ → SO3) (F : Vec3) (t : ℝ) :
    ‖errorFlow R F t‖ ≤ 1 := by
  apply (norm_mul_le _ _).trans
  calc
    _ ≤ 1*1 := mul_le_mul (rotation_norm_le _) (unmean_norm_le _ _) (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem errorFlow_norm (R : ℝ → SO3) (F : Vec3) (t : ℝ) :
    ‖errorFlow R F t‖ = 1 := by
  apply le_antisymm (errorFlow_norm_le R F t)
  have hh := (errorFlow R F t).le_opNorm anchor
  simpa only [errorFlow, ContinuousLinearMap.mul_apply, rotation_norm_apply,
    unmean_eq, mean_rotation, anchor_norm, mul_one] using hh

theorem errorFlow_mean (R : ℝ → SO3) (F : Vec3) (t : ℝ) :
    errorFlow R F t * mean F t = rotation (R t) := by
  simp [errorFlow, mul_assoc, unmean_mean]

theorem errorFlow_initial (R : ℝ → SO3) (F : Vec3) (hR₀ : R 0 = 1) :
    errorFlow R F 0 = 1 := by
  simp [errorFlow, unmean, hR₀, rotation, matrixOp]

theorem errorFlow_derivative (R : ℝ → SO3) (F G : Vec3)
    (hR : ∀ t, HasDerivAt (fun s => rotation (R s))
      (rotation (R t) * (hat F + (t-1/2) • hat G)) t) (t : ℝ) :
    HasDerivAt (errorFlow R F) (errorFlow R F t * residual F G t) t := by
  have hd := (hR t).mul (hasDerivAt_exp_smul_const' (-(hat F)) t)
  convert hd using 1
  change (rotation (R t) * unmean F t) *
      (mean F t * ((t-1/2) • hat G) * unmean F t) =
    (rotation (R t) * (hat F + (t-1/2) • hat G)) * unmean F t +
      rotation (R t) * ((-(hat F)) * unmean F t)
  calc
    _ = rotation (R t) * (unmean F t * mean F t) * ((t-1/2) • hat G) * unmean F t := by simp only [mul_assoc]
    _ = _ := by
      rw [unmean_mean, mul_one]
      have hc (A B C Q : Op) : A*C*Q = A*(B+C)*Q+A*((-B)*Q) := by
        have he : B+C+(-B) = C := by abel
        calc
          _ = A*(B+C+(-B))*Q := congrArg (fun x => A*x*Q) he.symm
          _ = _ := by simp only [mul_add, add_mul, mul_assoc]
      exact hc (rotation (R t)) (hat F) ((t-1/2) • hat G) (unmean F t)

def predictRotation (F G : Vec3) (N : ℕ) : Op :=
  Dyson.approx (residual F G) (N+3) 1 * mean F 1
def predictVelocity (F G : Vec3) (T : ℝ) (a₀ a₁ : E3) (N : ℕ) : E3 :=
  ∫ s in (0 : ℝ)..1, Dyson.approx (residual F G) (N+2) s (transported F T a₀ a₁ s)
def predictPosition (F G : Vec3) (T : ℝ) (a₀ a₁ : E3) (N : ℕ) : E3 :=
  T • ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..s,
    Dyson.approx (residual F G) (N+1) r (transported F T a₀ a₁ r)

theorem velocity_column_evaluation (B : ℝ → Op) (a : ℝ → E3)
    (hB : Continuous B) (ha : Continuous a) (n : ℕ) (t : ℝ) :
    Dyson.velocityApprox B (fun s => column (a s)) n t anchor =
      ∫ s in (0 : ℝ)..t, Dyson.approx B n s (a s) := by
  have hh := ContinuousLinearMap.intervalIntegral_apply (μ := MeasureTheory.volume)
    (((Dyson.approx_continuous B hB n).mul (column.continuous.comp ha)).intervalIntegrable 0 t) anchor
  simpa only [Dyson.velocityApprox, Function.comp_apply, Pi.mul_apply,
    ContinuousLinearMap.mul_apply, column_anchor] using hh

theorem position_column_evaluation (B : ℝ → Op) (a : ℝ → E3)
    (hB : Continuous B) (ha : Continuous a) (n : ℕ) (t : ℝ) :
    Dyson.positionApprox B (fun s => column (a s)) (n+1) t anchor =
      ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, Dyson.approx B n r (a r) := by
  change (∫ s in (0 : ℝ)..t, Dyson.velocityApprox B (fun s => column (a s)) n s) anchor = _
  have hh := ContinuousLinearMap.intervalIntegral_apply (μ := MeasureTheory.volume)
    ((Dyson.velocityApprox_continuous B _ hB (column.continuous.comp ha) n).intervalIntegrable 0 t) anchor
  simpa only [Function.comp_def, velocity_column_evaluation B a hB ha] using hh

/-- The paper's actual FOH theorem, in Euclidean physical outputs, at total
insertion depth D=N+2. Every analytic norm/envelope hypothesis of the generic
Dyson theorem is discharged here from rotation geometry and the FOH inputs.
The only trajectory hypotheses are the physical normalized-time ODE and its
identity/zero initial conditions. R is an actual SO(3)-valued trajectory. -/
theorem physical_remainder
    (R : ℝ → SO3) (v p : ℝ → E3) (F G : Vec3) {T : ℝ} (hT : 0 ≤ T)
    (a₀ a₁ : E3)
    (hR : ∀ t, HasDerivAt (fun s => rotation (R s))
      (rotation (R t) * (hat F + (t-1/2) • hat G)) t) (hR₀ : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotation (R t) (acceleration T a₀ a₁ t)) t) (hv₀ : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (T • v t) t) (hp₀ : p 0 = 0) (N : ℕ) :
    ‖rotation (R 1) - predictRotation F G N‖ ≤
      (enorm G/4)^(N+3) / ((N+3).factorial : ℝ) ∧
    ‖v 1 - predictVelocity F G T a₀ a₁ N‖ ≤
      ((enorm G/4)^(N+2) / ((N+2).factorial : ℝ)) * (T*(‖a₀‖+‖a₁‖)/2) ∧
    ‖p 1 - predictPosition F G T a₀ a₁ N‖ ≤
      T * (((enorm G/4)^(N+1) / ((N+1).factorial : ℝ)) * (T*(‖a₀‖+‖a₁‖)/2)) := by
  have hvc (t : ℝ) : HasDerivAt (fun s => column (v s))
      (errorFlow R F t * columnInput F T a₀ a₁ t) t := by
    have hh := column.hasFDerivAt.comp_hasDerivAt t (hv t)
    convert hh using 1
    rw [columnInput, column_mul, transported, ← ContinuousLinearMap.mul_apply, errorFlow_mean]
  have hpc (t : ℝ) : HasDerivAt (fun s => column (p s)) (T • column (v t)) t := by
    simpa only [map_smul] using column.hasFDerivAt.comp_hasDerivAt t (hp t)
  obtain ⟨hrot,hvel,hpos⟩ := Dyson.triangular_error_bound_centered_physical
    (residual F G) (errorFlow R F) (columnInput F T a₀ a₁)
    (fun t => column (v t)) (fun t => column (p t))
    (residual_continuous F G) (columnInput_continuous F T a₀ a₁)
    (errorFlow_derivative R F G hR) (errorFlow_initial R F hR₀)
    hvc (by simp [hv₀]) hT (show (0 : ℝ) ≤ 1 by norm_num) (enorm_nonneg G)
    hpc (by simp [hp₀]) (fun t _ => residual_norm_le F G t)
    (fun t _ => errorFlow_norm_le R F t) (impulse_bound F hT a₀ a₁) N
  simp only [one_mul] at hrot hvel hpos
  refine ⟨?_, ?_, ?_⟩
  · have he : rotation (R 1) - predictRotation F G N =
        (errorFlow R F 1 - Dyson.approx (residual F G) (N+3) 1) * mean F 1 := by
      rw [sub_mul, errorFlow_mean]; rfl
    rw [he]
    calc
      _ ≤ ‖errorFlow R F 1 - Dyson.approx (residual F G) (N+3) 1‖ * ‖mean F 1‖ := norm_mul_le _ _
      _ ≤ ‖errorFlow R F 1 - Dyson.approx (residual F G) (N+3) 1‖ * 1 :=
        mul_le_mul_of_nonneg_left (mean_norm_le F 1) (norm_nonneg _)
      _ ≤ _ := by simpa only [mul_one] using hrot
  · have hh := (column (v 1) - Dyson.velocityApprox (residual F G)
        (columnInput F T a₀ a₁) (N+2) 1).le_opNorm anchor
    rw [anchor_norm, mul_one] at hh
    have he := velocity_column_evaluation (residual F G) (transported F T a₀ a₁)
      (residual_continuous F G) (transported_continuous F T a₀ a₁) (N+2) 1
    change Dyson.velocityApprox (residual F G) (columnInput F T a₀ a₁) (N+2) 1 anchor =
      predictVelocity F G T a₀ a₁ N at he
    rw [ContinuousLinearMap.sub_apply, column_anchor, he] at hh
    exact hh.trans hvel
  · have hh := (column (p 1) - T • Dyson.positionApprox (residual F G)
        (columnInput F T a₀ a₁) (N+2) 1).le_opNorm anchor
    rw [anchor_norm, mul_one] at hh
    have he := position_column_evaluation (residual F G) (transported F T a₀ a₁)
      (residual_continuous F G) (transported_continuous F T a₀ a₁) (N+1) 1
    have he' : (T • Dyson.positionApprox (residual F G) (columnInput F T a₀ a₁) (N+2) 1) anchor =
        predictPosition F G T a₀ a₁ N := by
      change T • (Dyson.positionApprox (residual F G) (fun t => column (transported F T a₀ a₁ t))
        ((N+1)+1) 1 anchor) = _
      rw [he]; rfl
    rw [ContinuousLinearMap.sub_apply, column_anchor, he'] at hh
    exact hh.trans hpos

def meanAngle (T : ℝ) (ω₀ ω₁ : Vec3) : Vec3 := (T/2) • (ω₀+ω₁)
def slopeAngle (T : ℝ) (ω₀ ω₁ : Vec3) : Vec3 := T • (ω₁-ω₀)

theorem sampled_generator (T : ℝ) (ω₀ ω₁ : Vec3) (t : ℝ) :
    hat (meanAngle T ω₀ ω₁) + (t-1/2) • hat (slopeAngle T ω₀ ω₁) =
      hat (T • ((1-t) • ω₀ + t • ω₁)) := by
  unfold hat
  rw [← map_smul, ← map_add, ← skew_smul, ← skew_add]
  congr 2
  unfold meanAngle slopeAngle
  module

/-- Sample-based version: both sensor inputs are FOH. No norm assumption on
the rotation flow, conjugated gyro slope, or acceleration integral is supplied
by the caller. D=N+2 is the total insertion depth of the finite prediction. -/
theorem foh_remainder
    (R : ℝ → SO3) (v p : ℝ → E3) {T : ℝ} (hT : 0 ≤ T)
    (ω₀ ω₁ : Vec3) (a₀ a₁ : E3)
    (hR : ∀ t, HasDerivAt (fun s => rotation (R s))
      (rotation (R t) * hat (T • ((1-t) • ω₀ + t • ω₁))) t) (hR₀ : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotation (R t) (acceleration T a₀ a₁ t)) t) (hv₀ : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (T • v t) t) (hp₀ : p 0 = 0) (N : ℕ) :
    ‖rotation (R 1) - predictRotation (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) N‖ ≤
      (T*enorm (ω₁-ω₀)/4)^(N+3) / ((N+3).factorial : ℝ) ∧
    ‖v 1 - predictVelocity (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) T a₀ a₁ N‖ ≤
      ((T*enorm (ω₁-ω₀)/4)^(N+2) / ((N+2).factorial : ℝ)) * (T*(‖a₀‖+‖a₁‖)/2) ∧
    ‖p 1 - predictPosition (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁) T a₀ a₁ N‖ ≤
      T * (((T*enorm (ω₁-ω₀)/4)^(N+1) / ((N+1).factorial : ℝ)) * (T*(‖a₀‖+‖a₁‖)/2)) := by
  have hh := physical_remainder R v p (meanAngle T ω₀ ω₁) (slopeAngle T ω₀ ω₁)
    hT a₀ a₁ (fun t => by simpa only [sampled_generator] using hR t)
    hR₀ hv hv₀ hp hp₀ N
  simpa only [slopeAngle, enorm_smul, abs_of_nonneg hT] using hh

/-- Exact constant-gyro/FOH-accelerometer limit for the actual physical flow,
including velocity and position, at insertion depth two. -/
theorem constant_gyro_exact
    (R : ℝ → SO3) (v p : ℝ → E3) {T : ℝ} (hT : 0 ≤ T)
    (ω : Vec3) (a₀ a₁ : E3)
    (hR : ∀ t, HasDerivAt (fun s => rotation (R s)) (rotation (R t) * hat (T • ω)) t)
    (hR₀ : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotation (R t) (acceleration T a₀ a₁ t)) t) (hv₀ : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (T • v t) t) (hp₀ : p 0 = 0) :
    rotation (R 1) = predictRotation (meanAngle T ω ω) 0 0 ∧
    v 1 = predictVelocity (meanAngle T ω ω) 0 T a₀ a₁ 0 ∧
    p 1 = predictPosition (meanAngle T ω ω) 0 T a₀ a₁ 0 := by
  have he (t : ℝ) : (1-t) • ω + t • ω = ω := by module
  have hh := foh_remainder R v p hT ω ω a₀ a₁
    (fun t => by simpa only [he] using hR t) hR₀ hv hv₀ hp hp₀ 0
  simpa [slopeAngle, enorm, sub_eq_zero] using hh

end GNC.Preintegration.CenteredFoh
