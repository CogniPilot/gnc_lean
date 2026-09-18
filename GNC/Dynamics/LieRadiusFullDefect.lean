import GNC.Dynamics.LieRadiusDefect

/-! Full inverse-radius polynomial certification for arbitrary three-axis
attitude errors. The cubic inverse-radius factor and complete scalar
constraint are retained, rather than bounding their products separately.
This is needed when correlated initial translation is appreciable. -/
noncomputable section
namespace GNC
open Matrix Real Gravity LieRadiusDefect

theorem jacobianInverseQuadratic_residual_vector (φ v : Vec3) :
    enorm (Jacobian.leftAt φ (jacobianInverseQuadratic φ v)-v) ≤
      inverseQuadraticBudget (enorm φ)*enorm v := by
  by_cases hz : enorm φ=0
  · rw [(enorm_eq_zero_iff φ).mp hz]
    have h0 : enorm (0:Vec3)=0 := (enorm_eq_zero_iff _).mpr rfl
    simp [jacobianInverseQuadratic,Jacobian.leftAt,inverseQuadraticBudget,h0]
  · have hp : 0<enorm φ := lt_of_le_of_ne (enorm_nonneg φ) (Ne.symm hz)
    simpa only [Jacobian.unitAxis_reconstruct φ hp,abs_of_nonneg hp.le] using
      jacobianInverseQuadratic_residual_bound (Jacobian.unitAxis φ) v
        (Jacobian.unitAxis_unit φ hp) (enorm φ)

theorem jacobianInverseQuadratic_sub (φ v w : Vec3) :
    jacobianInverseQuadratic φ (v-w)=
      jacobianInverseQuadratic φ v-jacobianInverseQuadratic φ w := by
  simp only [jacobianInverseQuadratic,map_sub,LinearMap.sub_apply]
  module

namespace LieRadiusFullDefect

/-- Exact reference interpolation is charged after the approximate inverse.
This estimate is valid for a full attitude ball, including zero rotation. -/
theorem inverse_reference_bound (φ q qhat : Vec3) {σ δ : ℝ}
    (hφ : enorm φ<2*π) (hσ : enorm φ≤σ) (hδ : enorm (q-qhat)≤δ) :
    enorm (q-Jacobian.leftAt φ (jacobianInverseQuadratic φ qhat)) ≤
      inverseQuadraticBudget σ*enorm q+(1+σ/2+σ^2/12)*δ := by
  have hσ0 := (enorm_nonneg φ).trans hσ
  have hφ0 := enorm_nonneg φ
  have hd0 := (enorm_nonneg _).trans hδ
  have hres := jacobianInverseQuadratic_residual_vector φ q
  have hβ := inverseQuadraticBudget_mono (enorm_nonneg φ) hσ
  have hd := (leftAt_nonexpansive φ (jacobianInverseQuadratic φ (q-qhat)) hφ).trans
    (jacobianInverseQuadratic_bound φ (q-qhat))
  have hd' : enorm (Jacobian.leftAt φ (jacobianInverseQuadratic φ (q-qhat))) ≤
      (1+σ/2+σ^2/12)*δ := hd.trans (by gcongr <;> exact enorm_nonneg _)
  have hres' : enorm (q-Jacobian.leftAt φ (jacobianInverseQuadratic φ q)) ≤
      inverseQuadraticBudget σ*enorm q := by
    rw [show q-Jacobian.leftAt φ (jacobianInverseQuadratic φ q)=
      -(Jacobian.leftAt φ (jacobianInverseQuadratic φ q)-q) by module,enorm_neg]
    exact hres.trans (mul_le_mul_of_nonneg_right hβ (enorm_nonneg q))
  have he : q-Jacobian.leftAt φ (jacobianInverseQuadratic φ qhat)=
      (q-Jacobian.leftAt φ (jacobianInverseQuadratic φ q))+
        Jacobian.leftAt φ (jacobianInverseQuadratic φ (q-qhat)) := by
    rw [jacobianInverseQuadratic_sub,Jacobian.leftAt_sub]
    module
  rw [he]
  exact (enorm_add_le _ _).trans (add_le_add hres' hd')

theorem full_constraint_bound {s shat h H E C : ℝ}
    (hh : |h|≤H) (he : |s-shat|≤E)
    (hc : |(1+shat)*(1+h)^2-1|≤C) :
    |(1+s)*(1+h)^2-1|≤C+E*(1+H)^2 := by
  have hH := (abs_nonneg h).trans hh
  have hE := (abs_nonneg _).trans he
  have hh1 : |1+h|≤1+H := (abs_add_le 1 h).trans (by simpa using add_le_add_left hh 1)
  have hid : (1+s)*(1+h)^2-1=((1+shat)*(1+h)^2-1)+(s-shat)*(1+h)^2 := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_pow]
  exact add_le_add hc (mul_le_mul he (pow_le_pow_left₀ (abs_nonneg _) hh1 2) (by positivity) hE)

def budget (μ r σ P H δq δb E C R : ℝ) : ℝ :=
  let K := μ/r^3
  let A := (r+P)*(1+H)/r
  R+σ*δb+K*(3*H+3*H^2+H^3)*
    (inverseQuadraticBudget σ*r+(1+σ/2+σ^2/12)*δq)+
    μ*inverseRadiusFactor A/(r-P)^2*(C+E*(1+H)^2)

/-- Complete three-axis physical defect from a retained cubic Lie residual
and retained scalar inverse-radius constraint. All hypotheses concern known
candidate quantities. The true motion is not assumed to remain in a tube. -/
theorem physical_defect_bound (μ : ℝ) (hμ : 0≤μ) (φ q qhat ρ a b bhat : Vec3)
    (h shat : ℝ) (hr : 0<enorm q) (hφ : enorm φ<2*π)
    {σ P H δq δb E C R : ℝ} (hσ : enorm φ≤σ)
    (hρ : enorm ρ≤P) (hP : P<enorm q) (hh : |h|≤H) (hH : H<1)
    (hq : enorm (q-qhat)≤δq) (hb : enorm (b-bhat)≤δb)
    (he : |(enorm (q+Jacobian.leftAt φ ρ)^2/enorm q^2-1)-shat|≤E)
    (hc : |(1+shat)*(1+h)^2-1|≤C)
    (hR : enorm (a+(μ/enorm q^3*(1+h)^3) • ρ-φ ⨯₃ bhat+
      (μ/enorm q^3*((1+h)^3-1)) • jacobianInverseQuadratic φ qhat)≤R) :
    enorm (field3 μ q+b+Jacobian.leftAt φ a-
      (field3 μ (q+Jacobian.leftAt φ ρ)+rotate (rotationExp φ) b))≤
      budget μ (enorm q) σ P H δq δb E C R := by
  let r := enorm q
  let K := μ/r^3
  let u := (1+h)/r
  let A := (r+P)*(1+H)/r
  let w := jacobianInverseQuadratic φ qhat
  have hP0 := (enorm_nonneg ρ).trans hρ
  have hH0 := (abs_nonneg h).trans hh
  have hδb := (enorm_nonneg _).trans hb
  have hσ0 := (enorm_nonneg φ).trans hσ
  have hK : 0≤K := by dsimp [K,r]; positivity
  have hfloor : 0<r-P := sub_pos.mpr hP
  have hu : 0≤u := inverse_radius_branch hr hh hH
  have hrad := candidate_radius_bounds q φ ρ hφ hρ
  have hupp : u≤(1+H)/r := by
    apply div_le_div_of_nonneg_right _ hr.le
    linarith [(abs_le.mp hh).2]
  have hA : enorm (q+Jacobian.leftAt φ ρ)*u≤A := by
    calc
      _ ≤ (r+P)*((1+H)/r) := mul_le_mul hrad.2 hupp hu (by positivity)
      _ = A := by dsimp [A]; ring
  have hA0 : 0≤A := (mul_nonneg (enorm_nonneg _) hu).trans hA
  have hJ := inverse_reference_bound φ q qhat hφ hσ hq
  have hgain : |K*((1+h)^3-1)|≤K*(3*H+3*H^2+H^3) := by
    rw [abs_mul,abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left (inverse_cube_linear_bound hh) hK
  have hcub : μ*u^3=K*(1+h)^3 := by dsimp [u,K]; ring
  have hdiff : μ*u^3-radialGain μ q=K*((1+h)^3-1) := by
    rw [hcub]
    change K*(1+h)^3-K=_
    ring
  have hf : enorm (φ ⨯₃ (b-bhat))≤σ*δb :=
    (cross_enorm_le φ (b-bhat)).trans (mul_le_mul hσ hb (enorm_nonneg _) hσ0)
  have hres : enorm (a+(K*(1+h)^3) • ρ-φ ⨯₃ b+(K*((1+h)^3-1)) • w)≤R+σ*δb := by
    have hid : a+(K*(1+h)^3) • ρ-φ ⨯₃ b+(K*((1+h)^3-1)) • w=
        (a+(K*(1+h)^3) • ρ-φ ⨯₃ bhat+(K*((1+h)^3-1)) • w)-φ ⨯₃ (b-bhat) := by
      simp only [map_sub,LinearMap.sub_apply]
      module
    rw [hid]
    have hn := enorm_add_le
      (a+(K*(1+h)^3) • ρ-φ ⨯₃ bhat+(K*((1+h)^3-1)) • w) (-(φ ⨯₃ (b-bhat)))
    simpa only [enorm_neg,←sub_eq_add_neg] using hn.trans (add_le_add hR (by simpa only [enorm_neg] using hf))
  have hconstraint := full_constraint_bound hh he hc
  have heq : enorm (q+Jacobian.leftAt φ ρ)^2*u^2-1=
      (1+(enorm (q+Jacobian.leftAt φ ρ)^2/r^2-1))*(1+h)^2-1 := by
    dsimp [u]
    ring
  have htotal := lie_acceleration_defect_bound μ u hμ φ q ρ a b w hφ hfloor hrad.1 hu hA
  rw [hdiff,hcub,heq] at htotal
  have hfactor : 0≤μ*inverseRadiusFactor A/(r-P)^2 := by
    exact div_nonneg (mul_nonneg hμ (inverseRadiusFactor_nonnegative hA0)) (sq_nonneg _)
  exact htotal.trans (add_le_add (add_le_add hres
    (mul_le_mul hgain hJ (enorm_nonneg _) (by positivity)))
    (mul_le_mul_of_nonneg_left hconstraint hfactor))

end LieRadiusFullDefect
end GNC
