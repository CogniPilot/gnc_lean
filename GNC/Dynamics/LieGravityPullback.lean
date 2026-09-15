import GNC.Dynamics.GravityLinearization
import GNC.Lie.ZeroAttitude

/-! Exact orbital gravity and thrust in fixed-offset Lie translation coordinates.

No gravity truncation is used. A fixed inertial attitude offset permits a
constant SO(3) Jacobian. Its inverse makes the thrust discrepancy linear in
the rotation vector and removes one Jacobian from the radial gravity term.
These are reductions of the nonlinear equation, not a closed-form solution.
-/
noncomputable section
namespace GNC
open Matrix Real
open scoped Matrix Matrix.Norms.Operator

theorem jacobianMatrix_skew (q : Vec3) :
    jacobianMatrix q*skew q=(rotationExp q).val-1 := by
  by_cases hq : enorm q=0
  · rw [(enorm_eq_zero_iff q).mp hq]
    simp [jacobianMatrix,rotationExp,skew_zero]
  rw [jacobianMatrix,add_mul,add_mul,one_mul,Matrix.smul_mul,Matrix.smul_mul,
    ←pow_two,←pow_succ,skew_cube,rotationExp_formula]
  match_scalars <;> field_simp <;> ring

/-- J(q)(q × a) is exactly the finite rotation discrepancy, including q=0. -/
theorem leftAt_cross_rotation (q a : Vec3) :
    Jacobian.leftAt q (q ⨯₃ a)=rotate (rotationExp q) a-a := by
  rw [←jacobianMatrix_mulVec,←skew_mulVec,Matrix.mulVec_mulVec,jacobianMatrix_skew,
    Matrix.sub_mulVec,Matrix.one_mulVec]
  rfl

/-- The finite-angle thrust input is linear after the exact pullback. -/
theorem inverseAt_thrust (q a : Vec3) (hq : enorm q<2*π) :
    Jacobian.inverseAt q (rotate (rotationExp q) a-a)=q ⨯₃ a := by
  rw [←leftAt_cross_rotation,Jacobian.inverseAt_leftAt_all q _ hq]

/-- Differentiate the pulled-back vector with a fixed attitude offset.
The zero-angle case is included; no derivative of a singular quotient is used. -/
theorem inverseAt_fixed_derivative (φ : Vec3) {f : ℝ → Vec3} {v : Vec3} {t : ℝ}
    (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => Jacobian.inverseAt φ (f s)) (Jacobian.inverseAt φ v) t := by
  have hx := Jacobian.cross_derivative (hasDerivAt_const t φ) hf
  have hxx := Jacobian.cross_derivative (hasDerivAt_const t φ) hx
  simpa only [Jacobian.inverseAt, map_zero, LinearMap.zero_apply, zero_add] using
    (hf.sub (hx.const_smul (1/2:ℝ))).add
      (hxx.const_smul (Coefficients.beta (enorm φ)/enorm φ^2))

namespace Gravity

def radialGain (μ : ℝ) (q : Vec3) : ℝ := μ/enorm q^3

theorem field3_radial (μ : ℝ) (q : Vec3) :
    field3 μ q= -radialGain μ q • q := by
  simp [field3,field,radialGain,enorm,neg_div]

/-- Exact inverse-square gravity in pulled-back displacement coordinates.
Only the scalar gain and the transformed reference vector remain nonlinear. -/
theorem radial_pullback (μ : ℝ) (φ q ρ : Vec3) (hφ : enorm φ<2*π) :
    Jacobian.inverseAt φ
      (field3 μ (q+Jacobian.leftAt φ ρ)-field3 μ q)=
    -radialGain μ (q+Jacobian.leftAt φ ρ) • ρ-
      (radialGain μ (q+Jacobian.leftAt φ ρ)-radialGain μ q) •
        Jacobian.inverseAt φ q := by
  rw [field3_radial,field3_radial]
  simp only [Jacobian.inverseAt,smul_sub,smul_add,map_sub,map_add,map_smul]
  have he := Jacobian.inverseAt_leftAt_all φ ρ hφ
  dsimp [Jacobian.inverseAt] at he
  linear_combination (norm := module)
    (-radialGain μ (q+Jacobian.leftAt φ ρ)) • he

/-- Complete transformed gravity plus thrust. No fitted error allowance. -/
theorem radial_thrust_pullback (μ : ℝ) (φ q ρ a : Vec3) (hφ : enorm φ<2*π) :
    Jacobian.inverseAt φ
      (field3 μ (q+Jacobian.leftAt φ ρ)-field3 μ q+
        (rotate (rotationExp φ) a-a))=
    -radialGain μ (q+Jacobian.leftAt φ ρ) • ρ-
      (radialGain μ (q+Jacobian.leftAt φ ρ)-radialGain μ q) •
        Jacobian.inverseAt φ q+φ ⨯₃ a := by
  rw [Jacobian.inverseAt_add,radial_pullback μ φ q ρ hφ,inverseAt_thrust φ a hφ]

/-- Actual physical spacecraft and reference equations imply the reduced
nonlinear Lie-translation equation. Both trajectories may thrust and gravity
depends on their respective positions. The offset is fixed in inertial axes;
time-dependent offsets require additional Jacobian derivative terms. -/
theorem fixedOffset_error_dynamics (μ : ℝ) (φ : Vec3) (hφ : enorm φ<2*π)
    {p q v w b : ℝ → Vec3} {t : ℝ}
    (hp : HasDerivAt p (v t) t) (hq : HasDerivAt q (w t) t)
    (hv : HasDerivAt v (field3 μ (p t)+rotate (rotationExp φ) (b t)) t)
    (hw : HasDerivAt w (field3 μ (q t)+b t) t) :
    HasDerivAt (fun s => Jacobian.inverseAt φ (p s-q s))
      (Jacobian.inverseAt φ (v t-w t)) t ∧
    HasDerivAt (fun s => Jacobian.inverseAt φ (v s-w s))
      (-radialGain μ (p t) • Jacobian.inverseAt φ (p t-q t)-
        (radialGain μ (p t)-radialGain μ (q t)) • Jacobian.inverseAt φ (q t)+
        φ ⨯₃ b t) t := by
  refine ⟨inverseAt_fixed_derivative φ (hp.sub hq), ?_⟩
  have he : q t+Jacobian.leftAt φ (Jacobian.inverseAt φ (p t-q t))=p t := by
    rw [Jacobian.leftAt_inverseAt_all φ _ hφ]
    module
  have hg := radial_thrust_pullback μ φ (q t)
    (Jacobian.inverseAt φ (p t-q t)) (b t) hφ
  rw [he] at hg
  have ha : field3 μ (p t)+rotate (rotationExp φ) (b t)-(field3 μ (q t)+b t)=
      field3 μ (p t)-field3 μ (q t)+(rotate (rotationExp φ) (b t)-b t) := by module
  have hd := inverseAt_fixed_derivative φ (hv.sub hw)
  rw [ha,hg] at hd
  exact hd

/-- With zero gravity, the pulled-back relative acceleration has no nonlinear
angle term. This concerns prescribed matched thrust, without gyro or feedback
state augmentation. -/
theorem fixedOffset_gravityFree (φ : Vec3) (hφ : enorm φ<2*π)
    {v w b : ℝ → Vec3} {t : ℝ}
    (hv : HasDerivAt v (rotate (rotationExp φ) (b t)) t)
    (hw : HasDerivAt w (b t) t) :
    HasDerivAt (fun s => Jacobian.inverseAt φ (v s-w s)) (φ ⨯₃ b t) t := by
  have h := inverseAt_fixed_derivative φ (hv.sub hw)
  rw [inverseAt_thrust φ (b t) hφ] at h
  exact h

end Gravity
end GNC
