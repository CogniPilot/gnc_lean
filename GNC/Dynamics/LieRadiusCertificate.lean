import GNC.Dynamics.LieErrorReconstruction
import GNC.Dynamics.InverseRadius

/-! Scalar radius certificates without expanding Cartesian translation jets.

The factor theta*z is the Lie translation. Its exact SE2(3) reconstruction
has a squared norm containing only cos(theta), even though its vector
components contain both sine and cosine. This identity retains the
correlations needed by the inverse-radius gravity certificate.
-/
noncomputable section
namespace GNC
open Matrix Real

def jacobianInverseQuadratic (φ v : Vec3) : Vec3 :=
  v-(1/2:ℝ) • (φ ⨯₃ v)+(1/12:ℝ) • (φ ⨯₃ (φ ⨯₃ v))

theorem jacobianInverseQuadratic_bound (φ v : Vec3) :
    enorm (jacobianInverseQuadratic φ v)≤
      (1+enorm φ/2+enorm φ^2/12)*enorm v := by
  have h1 := cross_enorm_le φ v
  have h2 := (cross_enorm_le φ (φ ⨯₃ v)).trans
    (mul_le_mul_of_nonneg_left h1 (enorm_nonneg φ))
  unfold jacobianInverseQuadratic
  have ha := (enorm_add_le _ _).trans (add_le_add
    (enorm_add_le v (-((1/2:ℝ) • (φ ⨯₃ v)))) le_rfl)
  simp only [sub_eq_add_neg,enorm_neg,enorm_smul] at *
  norm_num at ha
  nlinarith

def inverseQuadraticOdd (θ : ℝ) : ℝ := θ^5/1440-θ^7/24192+θ^9/483840
def inverseQuadraticEven (θ : ℝ) : ℝ := -θ^4/720+θ^6/5040-θ^8/241920

/-- The finite polynomial part of J*P-I, derived using the cross-product
minimal polynomial. These coefficients are not fitted tolerances. -/
theorem inverseQuadratic_polynomial_residual (k v : Vec3) (hk : k ⬝ᵥ k=1) (θ : ℝ) :
    polynomialTranslation k (jacobianInverseQuadratic (θ • k) v) θ-θ • v=
      θ • (inverseQuadraticOdd θ • (k ⨯₃ v)+
        inverseQuadraticEven θ • (k ⨯₃ (k ⨯₃ v))) := by
  have h3 : k ⨯₃ (k ⨯₃ (k ⨯₃ v))= -(k ⨯₃ v) := by
    rw [Axis.cross_sq k v hk]
    simp only [map_sub,Axis.cross_axial,zero_sub]
  have h4 : k ⨯₃ (k ⨯₃ (k ⨯₃ (k ⨯₃ v)))= -(k ⨯₃ (k ⨯₃ v)) := by
    rw [h3,map_neg]
  simp only [polynomialTranslation,jacobianInverseQuadratic,map_smul,LinearMap.smul_apply,
    smul_smul,map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply,h3,h4,map_neg]
  unfold inverseQuadraticOdd inverseQuadraticEven OcticPointing.sine OcticPointing.cosineLoss
  module

/-- A fully explicit relative residual bound for the quadratic inverse.
This includes the sine/cosine Taylor tails and remains valid at zero angle. -/
def inverseQuadraticBudget (x : ℝ) : ℝ :=
  x^4/720+x^5/1440+x^6/5040+x^7/24192+x^8/241920+x^9/483840+
    (x^8/362880+x^9/3628800)*(1+x/2+x^2/12)

theorem inverseQuadratic_coefficients_bound (θ : ℝ) :
    |inverseQuadraticOdd θ|+|inverseQuadraticEven θ|≤
      |θ|^4/720+|θ|^5/1440+|θ|^6/5040+|θ|^7/24192+|θ|^8/241920+|θ|^9/483840 := by
  have h1 := (abs_add_le (θ^5/1440-θ^7/24192) (θ^9/483840)).trans
    (add_le_add (abs_sub_le (θ^5/1440) (θ^7/24192)) le_rfl)
  have h2 := (abs_sub_le (-θ^4/720+θ^6/5040) (θ^8/241920)).trans
    (add_le_add (abs_add_le (-θ^4/720) (θ^6/5040)) le_rfl)
  dsimp [inverseQuadraticOdd,inverseQuadraticEven]
  norm_num [abs_div,abs_pow] at h1 h2
  nlinarith

/-- Exact Gram reduction of the factored exponential translation.
No small-angle assumption or series truncation is used. -/
theorem factoredTranslation_lengthSq (k z : Vec3) (hk : k ⬝ᵥ k=1) (θ : ℝ) :
    lengthSq (factoredTranslation k z θ)=
      θ^2*(k ⬝ᵥ z)^2+2*(1-cos θ)*(lengthSq z-(k ⬝ᵥ z)^2) := by
  have he : factoredTranslation k z θ=
      sin θ • z+(1-cos θ) • (k ⨯₃ z)+((θ-sin θ)*(k ⬝ᵥ z)) • k := by
    rw [factoredTranslation,Axis.cross_sq k z hk]
    simp only [Axis.axial,smul_sub,smul_smul]
    module
  rw [he,←dot_self_lengthSq]
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,
    smul_eq_mul,cross_dot_cross,hk,dot_self_cross,dot_cross_self,
    dotProduct_comm z k,dotProduct_comm (k ⨯₃ z) z,
    dotProduct_comm (k ⨯₃ z) k,dot_self_lengthSq]
  nlinarith [congrArg (fun a : ℝ => a*(lengthSq z-(k ⬝ᵥ z)^2)) (sin_sq_add_cos_sq θ)]

/-- Scalar squared radius of a reconstructed position. Only three linear
reference projections and the axial/transverse Gram terms are needed. -/
def factoredRadiusSq (q k z : Vec3) (θ : ℝ) : ℝ :=
  lengthSq q+2*(θ*(q ⬝ᵥ z)+(1-cos θ)*(q ⬝ᵥ (k ⨯₃ z))+
    (θ-sin θ)*(q ⬝ᵥ (k ⨯₃ (k ⨯₃ z))))+
    θ^2*(k ⬝ᵥ z)^2+2*(1-cos θ)*(lengthSq z-(k ⬝ᵥ z)^2)

theorem factoredRadiusSq_eq (q k z : Vec3) (hk : k ⬝ᵥ k=1) (θ : ℝ) :
    factoredRadiusSq q k z θ=enorm (q+factoredTranslation k z θ)^2 := by
  rw [enorm_sq]
  have he : lengthSq (q+factoredTranslation k z θ)=lengthSq q+
      2*(q ⬝ᵥ factoredTranslation k z θ)+lengthSq (factoredTranslation k z θ) := by
    simp only [←dot_self_lengthSq,add_dotProduct,dotProduct_add,
      dotProduct_comm (factoredTranslation k z θ) q]
    ring
  rw [he,factoredTranslation_lengthSq k z hk θ]
  simp only [factoredRadiusSq,factoredTranslation,dotProduct_add,dotProduct_smul,
    smul_eq_mul]
  ring

namespace Gravity

/-- Separate the small products in the normalized inverse-radius constraint.
The scalar u is the squared-radius deviation; h is the inverse-radius offset. -/
theorem radius_constraint_split (u h : ℝ) :
    (1+u)*(1+h)^2-1=(u+2*h)+h^2+2*u*h+u*h^2 := by ring

theorem radius_constraint_bound {u h U H : ℝ} (hu : |u|≤U) (hh : |h|≤H) :
    |(1+u)*(1+h)^2-1|≤|u+2*h|+H^2+2*U*H+U*H^2 := by
  have hu0 := (abs_nonneg u).trans hu
  have hh0 := (abs_nonneg h).trans hh
  rw [radius_constraint_split]
  calc
    |u+2*h+h^2+2*u*h+u*h^2|≤|u+2*h|+|h^2|+|2*u*h|+|u*h^2| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ = |u+2*h|+|h|^2+2*|u| * |h|+|u| * |h|^2 := by
      simp [abs_mul,abs_pow]
    _ ≤ _ := by gcongr

/-- Quadratic displacement growth makes the omitted constraint products
fourth and sixth order in time; no constant worst-case allowance is needed. -/
theorem radius_constraint_time_bound {u h U H t : ℝ}
    (hu : |u|≤U*t^2) (hh : |h|≤H*t^2) :
    |(1+u)*(1+h)^2-1|≤|u+2*h|+(H^2+2*U*H)*t^4+U*H^2*t^6 := by
  convert radius_constraint_bound hu hh using 1
  ring

/-- The inverse-cube polynomial needs only its linear term in the checked
residual; the omitted products have this explicit time-dependent budget. -/
theorem inverse_cube_offset_time_bound {h H t : ℝ} (hh : |h|≤H*t^2) :
    |(1+h)^3-1-3*h|≤3*H^2*t^4+H^3*t^6 := by
  have hH := (abs_nonneg h).trans hh
  calc
    |(1+h)^3-1-3*h|=|3*h^2+h^3| := by congr 1; ring
    _ ≤ 3*|h|^2+|h|^3 := by
      have htri := abs_add_le (3*h^2) (h^3)
      rw [abs_of_nonneg (by positivity : (0:ℝ)≤3*h^2),abs_pow] at htri
      simpa only [sq_abs] using htri
    _ ≤ 3*(H*t^2)^2+(H*t^2)^3 := by gcongr
    _ = _ := by ring

/-- Full inverse-square gravity can be certified using the scalar Gram
expression. The candidate inverse radius must use the nonnegative branch. -/
theorem factored_field_inverse_radius_bound (μ : ℝ) (hμ : 0≤μ)
    (q k z : Vec3) (hk : k ⬝ᵥ k=1) (θ : ℝ) {u m A : ℝ}
    (hm : 0<m) (hr : m≤enorm (q+factoredTranslation k z θ))
    (hu : 0≤u) (hA : enorm (q+factoredTranslation k z θ)*u≤A) :
    enorm (field3 μ (q+factoredTranslation k z θ)-
      (-μ*u^3) • (q+factoredTranslation k z θ))≤
      μ*inverseRadiusFactor A/m^2*|factoredRadiusSq q k z θ*u^2-1| := by
  rw [factoredRadiusSq_eq q k z hk θ]
  exact field_inverse_radius_bound μ hμ (WithLp.toLp 2 (q+factoredTranslation k z θ))
    hm hr hu hA

/-- Exact preconditioned acceleration defect. The freely chosen w
approximates J(phi)^{-1}q; its residual is charged explicitly. This avoids
expanding the reconstructed trajectory into a Cartesian polynomial. -/
theorem lie_acceleration_defect (μ u : ℝ) (φ q ρ a b w : Vec3) :
    field3 μ q+b+Jacobian.leftAt φ a-
      (field3 μ (q+Jacobian.leftAt φ ρ)+rotate (rotationExp φ) b)=
    Jacobian.leftAt φ (a+(μ*u^3) • ρ-φ ⨯₃ b+
      (μ*u^3-radialGain μ q) • w)+
    (μ*u^3-radialGain μ q) • (q-Jacobian.leftAt φ w)+
    ((-μ*u^3) • (q+Jacobian.leftAt φ ρ)-field3 μ (q+Jacobian.leftAt φ ρ)) := by
  rw [Jacobian.leftAt_add,Jacobian.leftAt_sub,Jacobian.leftAt_add,
    Jacobian.leftAt_smul,Jacobian.leftAt_smul,leftAt_cross_rotation,field3_radial]
  module

/-- The physical defect bound uses a Lie residual, a Jacobian inverse
residual, and a scalar full-gravity constraint. No unknown trajectory or
unquantified Taylor allowance enters this pointwise inequality. -/
theorem lie_acceleration_defect_bound (μ u : ℝ) (hμ : 0≤μ)
    (φ q ρ a b w : Vec3) (hφ : enorm φ<2*π) {m A : ℝ}
    (hm : 0<m) (hr : m≤enorm (q+Jacobian.leftAt φ ρ))
    (hu : 0≤u) (hA : enorm (q+Jacobian.leftAt φ ρ)*u≤A) :
    enorm (field3 μ q+b+Jacobian.leftAt φ a-
      (field3 μ (q+Jacobian.leftAt φ ρ)+rotate (rotationExp φ) b))≤
    enorm (a+(μ*u^3) • ρ-φ ⨯₃ b+(μ*u^3-radialGain μ q) • w)+
    |μ*u^3-radialGain μ q| * enorm (q-Jacobian.leftAt φ w)+
    μ*inverseRadiusFactor A/m^2*|enorm (q+Jacobian.leftAt φ ρ)^2*u^2-1| := by
  rw [lie_acceleration_defect μ u φ q ρ a b w]
  apply (enorm_add_le _ _).trans
  apply add_le_add
  · apply (enorm_add_le _ _).trans
    rw [enorm_smul]
    exact add_le_add (leftAt_nonexpansive φ _ hφ) le_rfl
  · have h := field_inverse_radius_bound μ hμ (WithLp.toLp 2 (q+Jacobian.leftAt φ ρ))
      hm hr hu hA
    simpa only [norm_sub_rev] using h

end Gravity

end GNC
