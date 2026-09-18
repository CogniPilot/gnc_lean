import GNC.Dynamics.LieRadiusFullDefect
import GNC.Lie.JacobianPolynomial

/-! Transfer a checked enclosure of the candidate's cubic inverse-radius
factor into the full nonlinear gravity defect. This connects scalar product
certificates to the physical residual; the radius constraint remains an
explicit, separate obligation. -/
noncomputable section
namespace GNC.LieRadiusFullDefect
open Matrix Real Gravity

/-- Factor the shared nonlinear gravity coefficient before polynomial
multiplication. The joint factor retains cancellations between its inputs. -/
theorem coupled_residual_identity (K c : ℝ) (a ρ φ b w : Vec3) :
    a+(K*c) • ρ-φ ⨯₃ b+(K*(c-1)) • w=
      a+K • ρ-φ ⨯₃ b+(K*(c-1)) • (ρ+w) := by module

/-- The quadratic skew correction contracts when its transverse multiplier
lies between minus one and one. The condition is derived from its Gram form. -/
theorem quadratic_skew_nonexpansive (φ q : Vec3) (b : ℝ)
    (hb : 0≤b) (hbφ : b*lengthSq φ≤2) :
    enorm (q+b • (φ ⨯₃ (φ ⨯₃ q)))≤enorm q := by
  have hg := JacobianPolynomial.gram φ q 0 b
  simp only [zero_smul,add_zero] at hg
  have hs : (0:ℝ)^2-2*b+lengthSq φ*b^2≤0 := by
    have he : (0:ℝ)^2-2*b+lengthSq φ*b^2=b*(b*lengthSq φ-2) := by ring
    rw [he]
    exact mul_nonpos_of_nonneg_of_nonpos hb (sub_nonpos.mpr hbφ)
  have hd := mul_nonpos_of_nonpos_of_nonneg hs (sq_nonneg (enorm (φ ⨯₃ q)))
  nlinarith [enorm_nonneg q,enorm_nonneg (q+b • (φ ⨯₃ (φ ⨯₃ q)))]

/-- Center the coupled gravity multiplier at the midpoint family's exact
initial Lie error. The linear skew terms cancel; the constant 24 is
2/(1/12), from the quadratic inverse-Jacobian coefficient. -/
theorem midpoint_multiplier_bound (φ q ρ : Vec3) (hφ : enorm φ^2≤24) :
    enorm (ρ+jacobianInverseQuadratic φ q)≤
      enorm q+enorm (ρ-(1/2:ℝ) • (φ ⨯₃ q)) := by
  have hb : (1/12:ℝ)*lengthSq φ≤2 := by rw [←enorm_sq]; linarith
  have hn := quadratic_skew_nonexpansive φ q (1/12) (by norm_num) hb
  have he : ρ+jacobianInverseQuadratic φ q=
      (q+(1/12:ℝ) • (φ ⨯₃ (φ ⨯₃ q)))+(ρ-(1/2:ℝ) • (φ ⨯₃ q)) := by
    unfold jacobianInverseQuadratic
    module
  rw [he]
  exact (enorm_add_le _ _).trans (add_le_add hn le_rfl)

theorem midpoint_initial_multiplier_bound (φ q : Vec3) (hφ : enorm φ^2≤24) :
    enorm ((1/2:ℝ) • (φ ⨯₃ q)+jacobianInverseQuadratic φ q)≤enorm q := by
  have h := midpoint_multiplier_bound φ q ((1/2:ℝ) • (φ ⨯₃ q)) hφ
  have hz : enorm (0:Vec3)=0 := (enorm_eq_zero_iff _).mpr rfl
  simpa only [sub_self,hz,add_zero] using h

/-- Replacing the cubic factor incurs its error in both gravity terms. -/
theorem cubic_residual_bound (K h c ε R : ℝ) (a ρ φ b w : Vec3)
    (hK : 0≤K) (hc : |(1+h)^3-c|≤ε)
    (hR : enorm (a+(K*c) • ρ-φ ⨯₃ b+(K*(c-1)) • w)≤R) :
    enorm (a+(K*(1+h)^3) • ρ-φ ⨯₃ b+(K*((1+h)^3-1)) • w)≤
      R+K*ε*enorm (ρ+w) := by
  have he : a+(K*(1+h)^3) • ρ-φ ⨯₃ b+(K*((1+h)^3-1)) • w=
      (a+(K*c) • ρ-φ ⨯₃ b+(K*(c-1)) • w)+
        (K*((1+h)^3-c)) • (ρ+w) := by module
  have hn : enorm ((K*((1+h)^3-c)) • (ρ+w))≤K*ε*enorm (ρ+w) := by
    rw [enorm_smul,abs_mul,abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hK) (enorm_nonneg _)
  rw [he]
  exact (enorm_add_le _ _).trans (add_le_add hR hn)

/-- A weaker version is available when only separate factor norms are known. -/
theorem cubic_residual_bound_separate (K h c ε R : ℝ) (a ρ φ b w : Vec3)
    (hK : 0≤K) (hc : |(1+h)^3-c|≤ε)
    (hR : enorm (a+(K*c) • ρ-φ ⨯₃ b+(K*(c-1)) • w)≤R) :
    enorm (a+(K*(1+h)^3) • ρ-φ ⨯₃ b+(K*((1+h)^3-1)) • w)≤
      R+K*ε*(enorm ρ+enorm w) :=
  (cubic_residual_bound K h c ε R a ρ φ b w hK hc hR).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (enorm_add_le ρ w)
      (mul_nonneg hK ((abs_nonneg _).trans hc))))

/-- Physical specialization: a cubic enclosure can be supplied directly.
Its remainder is charged separately from the scalar radius constraint and
the approximate inverse-Jacobian error. No exact-radius assumption on h is
introduced by replacing its cubic polynomial. -/
theorem physical_defect_of_cubic_enclosure
    (μ : ℝ) (hμ : 0≤μ) (φ q qhat ρ a b bhat : Vec3)
    (h shat c : ℝ) (hr : 0<enorm q) (hφ : enorm φ<2*π)
    {σ P H δq δb E C R ε : ℝ} (hσ : enorm φ≤σ)
    (hρ : enorm ρ≤P) (hP : P<enorm q) (hh : |h|≤H) (hH : H<1)
    (hq : enorm (q-qhat)≤δq) (hb : enorm (b-bhat)≤δb)
    (he : |(enorm (q+Jacobian.leftAt φ ρ)^2/enorm q^2-1)-shat|≤E)
    (hc : |(1+shat)*(1+h)^2-1|≤C)
    (hcubic : |(1+h)^3-c|≤ε)
    (hR : enorm (a+(μ/enorm q^3*c) • ρ-φ ⨯₃ bhat+
      (μ/enorm q^3*(c-1)) • jacobianInverseQuadratic φ qhat)≤R) :
    enorm (field3 μ q+b+Jacobian.leftAt φ a-
      (field3 μ (q+Jacobian.leftAt φ ρ)+rotate (rotationExp φ) b))≤
      budget μ (enorm q) σ P H δq δb E C
        (R+(μ/enorm q^3)*ε*enorm (ρ+jacobianInverseQuadratic φ qhat)) := by
  have hK : 0≤μ/enorm q^3 := div_nonneg hμ (pow_nonneg hr.le _)
  exact physical_defect_bound μ hμ φ q qhat ρ a b bhat h shat hr hφ
    hσ hρ hP hh hH hq hb he hc
    (cubic_residual_bound (μ/enorm q^3) h c ε R a ρ φ bhat
      (jacobianInverseQuadratic φ qhat) hK hcubic hR)

end GNC.LieRadiusFullDefect
