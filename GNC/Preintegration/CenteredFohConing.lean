import GNC.Analysis.OrderedQuadratic
import GNC.Preintegration.CenteredFohWeightedBounds
import GNC.Lie.CayleyChart
import GNC.Lie.Adjoint

/-! Compact second-order residual-rotation construction for centered FOH.
The cross-product term is an exact rewriting of the finite ordered integral,
including the sign for the right-flow convention. No log chart or division
by mean angle is required. The raw finite matrix need not be orthogonal. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
namespace GNC.Preintegration.CenteredFoh.Coning

def hatLinear : Vec3 →L[ℝ] Op :=
  matrixOp.toAlgEquiv.toLinearMap.toContinuousLinearMap.comp
    Cayley.skewLinear.toContinuousLinearMap

@[simp] theorem hatLinear_apply (v : Vec3) : hatLinear v = hat v := rfl

theorem hat_smul (r : ℝ) (v : Vec3) : hat (r • v) = r • hat v := by
  exact hatLinear.map_smul r v

theorem hat_cross (u v : Vec3) : hat (u ⨯₃ v) = hat u * hat v - hat v * hat u := by
  simp only [hat, skew_cross, map_sub, map_mul]

theorem hat_integral (b : ℝ → Vec3) (hb : Continuous b) (t : ℝ) :
    hat (∫ s in (0 : ℝ)..t, b s) = ∫ s in (0 : ℝ)..t, hat (b s) :=
  (hatLinear.intervalIntegral_comp_comm (hb.intervalIntegrable 0 t)).symm

def first (b : ℝ → Vec3) (t : ℝ) : Vec3 := ∫ s in (0 : ℝ)..t, b s
def second (b : ℝ → Vec3) (t : ℝ) : Vec3 :=
  (1/2 : ℝ) • ∫ s in (0 : ℝ)..t, first b s ⨯₃ b s
def compact (b : ℝ → Vec3) (t : ℝ) : Op :=
  1 + hat (first b t) + (1/2 : ℝ) • (hat (first b t) * hat (first b t)) +
    hat (second b t)

theorem first_continuous (b : ℝ → Vec3) (hb : Continuous b) : Continuous (first b) :=
  OrderedQuadratic.first_continuous b hb

theorem first_hat (b : ℝ → Vec3) (hb : Continuous b) (t : ℝ) :
    OrderedQuadratic.first (fun s => hat (b s)) t = hat (first b t) :=
  (hat_integral b hb t).symm

theorem second_hat (b : ℝ → Vec3) (hb : Continuous b) (t : ℝ) :
    OrderedQuadratic.coning (fun s => hat (b s)) t = hat (second b t) := by
  have hc : Continuous (fun s => first b s ⨯₃ b s) := by
    have hfirst := first_continuous b hb
    fun_prop
  rw [second, hat_smul, hat_integral _ hc]
  simp_rw [hat_cross, ← first_hat b hb]
  rfl

/-- Every continuous residual vector admits this exact finite coning rewrite. -/
theorem compact_eq_approx (b : ℝ → Vec3) (hb : Continuous b) (t : ℝ) :
    compact b t = Dyson.approx (fun s => hat (b s)) 3 t := by
  have hh : Continuous (fun s => hat (b s)) := hatLinear.continuous.comp hb
  rw [← OrderedQuadratic.predictor_eq_approx _ hh t]
  simp only [OrderedQuadratic.predictor, first_hat b hb, second_hat b hb, compact]

def generator (F G : Vec3) (t : ℝ) : Vec3 :=
  (t-1/2) • rotate (rotationExp (t • F)) G

theorem generator_continuous (F G : Vec3) : Continuous (generator F G) := by
  have hc : Continuous (fun t : ℝ => (rotationExp (t • F)).val) := by
    exact NormedSpace.exp_continuous.comp
      (Cayley.contDiff_skew.continuous.comp (continuous_id.smul continuous_const))
  exact (continuous_id.sub continuous_const).smul (hc.matrix_mulVec continuous_const)

/-- The vector generator is the actual mean-removed centered gyro generator. -/
theorem generator_hat (F G : Vec3) (t : ℝ) : hat (generator F G t) = residual F G t := by
  have he : hat (rotate (rotationExp (t • F)) G) * mean F t = mean F t * hat G := by
    rw [mean_rotation]
    change matrixOp (skew (rotate (rotationExp (t • F)) G)) *
      matrixOp (rotationExp (t • F)).val =
      matrixOp (rotationExp (t • F)).val * matrixOp (skew G)
    rw [← map_mul, ← map_mul, skew_rotate]
  calc
    hat (generator F G t) = (t-1/2) • hat (rotate (rotationExp (t • F)) G) :=
      hat_smul _ _
    _ = (t-1/2) • (mean F t * hat G * unmean F t) := by
      rw [← he, mul_assoc, mean_unmean, mul_one]
    _ = residual F G t := by
      ext x
      simp only [residual, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.mul_apply, map_smul]

theorem centered_compact_eq_approx (F G : Vec3) (t : ℝ) :
    compact (generator F G) t = Dyson.approx (residual F G) 3 t := by
  have h := compact_eq_approx (generator F G) (generator_continuous F G) t
  simpa only [generator_hat] using h

/-- This is the same raw attitude approximant used in the physical theorem. -/
theorem common_order_two_rotation (F G : Vec3) :
    commonOrderRotation F G 2 = compact (generator F G) 1 * mean F 1 := by
  rw [commonOrderRotation, centered_compact_eq_approx]

theorem common_order_two_velocity (F G : Vec3) (T : ℝ) (a₀ a₁ : E3) :
    commonOrderVelocity F G T a₀ a₁ 2 =
      ∫ s in (0 : ℝ)..1, compact (generator F G) s (transported F T a₀ a₁ s) := by
  simp only [commonOrderVelocity, centered_compact_eq_approx]

theorem common_order_two_position (F G : Vec3) (T : ℝ) (a₀ a₁ : E3) :
    commonOrderPosition F G T a₀ a₁ 2 =
      T • ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..s,
        compact (generator F G) r (transported F T a₀ a₁ r) := by
  simp only [commonOrderPosition, centered_compact_eq_approx]

/-- The compact construction inherits the complete physical remainder from
the actual FOH ODEs. This is an endpoint theorem, not just a formal series
identity or an assumed predictor equation. -/
theorem compact_physical_remainder
    (R : ℝ → SO3) (v p : ℝ → E3) {T : ℝ} (hT : 0 ≤ T)
    (ω₀ ω₁ : Vec3) (a₀ a₁ : E3)
    (hR : ∀ t, HasDerivAt (fun s => rotation (R s))
      (rotation (R t) * hat (T • ((1-t) • ω₀ + t • ω₁))) t) (hR₀ : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotation (R t) (acceleration T a₀ a₁ t)) t) (hv₀ : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (T • v t) t) (hp₀ : p 0 = 0) :
    let F := meanAngle T ω₀ ω₁
    let G := slopeAngle T ω₀ ω₁
    let δ := (T*enorm (ω₁-ω₀)/4)^3/6
    ‖rotation (R 1) - compact (generator F G) 1 * mean F 1‖ ≤ δ ∧
    ‖v 1 - ∫ s in (0 : ℝ)..1,
      compact (generator F G) s (transported F T a₀ a₁ s)‖ ≤
      δ * T * Dyson.velocityWeight 3 ‖a₀‖ ‖a₁‖ ∧
    ‖p 1 - T • ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..s,
      compact (generator F G) r (transported F T a₀ a₁ r)‖ ≤
      δ * T^2 * Dyson.positionWeight 3 ‖a₀‖ ‖a₁‖ := by
  have h := common_order_weighted_foh_remainder R v p hT ω₀ ω₁ a₀ a₁
    hR hR₀ hv hv₀ hp hp₀ 2
  rw [common_order_two_rotation, common_order_two_velocity, common_order_two_position] at h
  simpa only [show (2+1 : ℕ) = 3 from rfl,
    show ((3 : ℕ).factorial : ℝ) = 6 from by norm_num] using h

end GNC.Preintegration.CenteredFoh.Coning
