import GNC.Dynamics.LieRadiusFullDefect
import GNC.Dynamics.LieRadiusSpatialApproximation
import GNC.Dynamics.LieGravityPullback

/-! A full-field residual certificate for Cartesian displacement predictors.
This gives a comparator the same scalar inverse-radius certificate used by
Lie candidates. The numerical integrator and tensor closure are irrelevant
to the proof: all their errors must appear in the candidate's residual.
-/
noncomputable section
namespace GNC.CartesianRadiusDefect
open Matrix Real Gravity LieRadiusDefect

theorem candidate_radius (q d : Vec3) {P : ℝ} (hd : enorm d≤P) :
    enorm q-P≤enorm (q+d) ∧ enorm (q+d)≤enorm q+P := by
  constructor
  · have h := enorm_add_le (q+d) (-d)
    rw [add_neg_cancel_right,enorm_neg] at h
    linarith
  · exact (enorm_add_le _ _).trans (add_le_add le_rfl hd)

/-- The same exact pointing geometry is available to Cartesian predictors;
only the polynomial query used to approximate its response is different. -/
theorem thrust_error (φ b bhat : Vec3) {σ δ B : ℝ}
    (hφ : enorm φ<2*π) (hσ : enorm φ≤σ)
    (hδ : enorm (b-bhat)≤δ) (hB : enorm bhat≤B) :
    enorm ((rotate (rotationExp φ) b-b)-
      JacobianPolynomial.apply φ (φ ⨯₃ bhat))≤
      σ*δ+JacobianPolynomial.tail σ*σ*B := by
  have hσ0 := (enorm_nonneg φ).trans hσ
  have hδ0 := (enorm_nonneg _).trans hδ
  have hB0 := (enorm_nonneg bhat).trans hB
  rw [←leftAt_cross_rotation]
  have he : Jacobian.leftAt φ (φ ⨯₃ b)-JacobianPolynomial.apply φ (φ ⨯₃ bhat)=
      Jacobian.leftAt φ (φ ⨯₃ (b-bhat))+
        (Jacobian.leftAt φ (φ ⨯₃ bhat)-JacobianPolynomial.apply φ (φ ⨯₃ bhat)) := by
    simp only [map_sub,Jacobian.leftAt_sub]
    module
  rw [he]
  apply (enorm_add_le _ _).trans
  apply add_le_add
  · exact (leftAt_nonexpansive φ _ hφ).trans
      ((cross_enorm_le _ _).trans (mul_le_mul hσ hδ (enorm_nonneg _) hσ0))
  · apply (JacobianPolynomial.error_bound φ (φ ⨯₃ bhat)).trans
    have hc := (cross_enorm_le φ bhat).trans
      (mul_le_mul hσ hB (enorm_nonneg _) hσ0)
    have ht := JacobianPolynomial.tail_mono (enorm_nonneg φ) hσ
    calc
      _≤JacobianPolynomial.tail σ*(σ*B) :=
        mul_le_mul ht hc (enorm_nonneg _) (JacobianPolynomial.tail_nonneg hσ0)
      _=_ := by ring

theorem residual_identity (μ u : ℝ) (q qhat d a f fhat : Vec3) :
    a-(field3 μ (q+d)-field3 μ q+f)=
      (a+(μ*u^3) • d+(μ*u^3-radialGain μ q) • qhat-fhat)+
      (μ*u^3-radialGain μ q) • (q-qhat)+(fhat-f)+
      ((-μ*u^3) • (q+d)-field3 μ (q+d)) := by
  rw [field3_radial μ q]
  module

def budget (μ r P H δq δf E C R : ℝ) : ℝ :=
  let A := (r+P)*(1+H)/r
  R+δf+(μ/r^3)*(3*H+3*H^2+H^3)*δq+
    μ*inverseRadiusFactor A/(r-P)^2*(C+E*(1+H)^2)

/-- Complete Cartesian acceleration-defect bound. All assumptions concern
the proposed displacement, reference, input and scalar inverse radius.
No actual orbit is assumed to stay in a tube. -/
theorem physical_defect_bound (μ : ℝ) (hμ : 0≤μ)
    (q qhat d a f fhat : Vec3) (h shat : ℝ) (hr : 0<enorm q)
    {P H δq δf E C R : ℝ}
    (hd : enorm d≤P) (hP : P<enorm q) (hh : |h|≤H) (hH : H<1)
    (hq : enorm (q-qhat)≤δq) (hf : enorm (f-fhat)≤δf)
    (he : |(enorm (q+d)^2/enorm q^2-1)-shat|≤E)
    (hc : |(1+shat)*(1+h)^2-1|≤C)
    (hR : enorm (a+(μ/enorm q^3*(1+h)^3) • d+
      (μ/enorm q^3*((1+h)^3-1)) • qhat-fhat)≤R) :
    enorm (a-(field3 μ (q+d)-field3 μ q+f))≤
      budget μ (enorm q) P H δq δf E C R := by
  let r := enorm q
  let K := μ/r^3
  let u := (1+h)/r
  let A := (r+P)*(1+H)/r
  have hP0 := (enorm_nonneg d).trans hd
  have hH0 := (abs_nonneg h).trans hh
  have hδq0 := (enorm_nonneg _).trans hq
  have hK : 0≤K := by dsimp [K,r]; positivity
  have hu : 0≤u := inverse_radius_branch hr hh hH
  have hrad := candidate_radius q d hd
  have hupp : u≤(1+H)/r := by
    apply div_le_div_of_nonneg_right _ hr.le
    linarith [(abs_le.mp hh).2]
  have hA : enorm (q+d)*u≤A := by
    calc
      _≤(r+P)*((1+H)/r) := mul_le_mul hrad.2 hupp hu (by positivity)
      _=A := by dsimp [A]; ring
  have hA0 : 0≤A := (mul_nonneg (enorm_nonneg _) hu).trans hA
  have hcub : μ*u^3=K*(1+h)^3 := by dsimp [u,K]; ring
  have hdiff : μ*u^3-radialGain μ q=K*((1+h)^3-1) := by
    rw [hcub]
    change K*(1+h)^3-K=_
    ring
  have hgain : |μ*u^3-radialGain μ q|≤K*(3*H+3*H^2+H^3) := by
    rw [hdiff,abs_mul,abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left (inverse_cube_linear_bound hh) hK
  have hres : enorm (a+(μ*u^3) • d+(μ*u^3-radialGain μ q) • qhat-fhat)≤R := by
    rw [hdiff,hcub]
    exact hR
  have hgravity := field_inverse_radius_bound μ hμ (WithLp.toLp 2 (q+d))
    (sub_pos.mpr hP) hrad.1 hu hA
  have hconstraint := LieRadiusFullDefect.full_constraint_bound hh he hc
  have heq : enorm (q+d)^2*u^2-1=
      (1+(enorm (q+d)^2/r^2-1))*(1+h)^2-1 := by dsimp [u]; ring
  have hfactor : 0≤μ*inverseRadiusFactor A/(r-P)^2 :=
    div_nonneg (mul_nonneg hμ (inverseRadiusFactor_nonnegative hA0)) (sq_nonneg _)
  have hg : enorm ((-μ*u^3) • (q+d)-field3 μ (q+d))≤
      μ*inverseRadiusFactor A/(r-P)^2*(C+E*(1+H)^2) := by
    have hg' : enorm ((-μ*u^3) • (q+d)-field3 μ (q+d))≤
        μ*inverseRadiusFactor A/(r-P)^2*|enorm (q+d)^2*u^2-1| := by
      simpa only [norm_sub_rev] using hgravity
    rw [heq] at hg'
    exact hg'.trans (mul_le_mul_of_nonneg_left hconstraint hfactor)
  rw [residual_identity μ u q qhat d a f fhat]
  have hmiddle : enorm ((μ*u^3-radialGain μ q) • (q-qhat))≤
      K*(3*H+3*H^2+H^3)*δq := by
    rw [enorm_smul]
    exact mul_le_mul hgain hq (enorm_nonneg _) (by positivity)
  have hforce : enorm (fhat-f)≤δf := by
    rw [show fhat-f= -(f-fhat) by module,enorm_neg]
    exact hf
  have htotal := (enorm_add_le _ _).trans
    (add_le_add ((enorm_add_le _ _).trans
      (add_le_add ((enorm_add_le _ _).trans (add_le_add hres hmiddle)) hforce)) hg)
  convert htotal using 1 <;> dsimp [budget,K,A,r] <;> ring

end GNC.CartesianRadiusDefect
