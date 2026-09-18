import GNC.Dynamics.LieRadiusApproximation

/-! A pointwise physical certificate assembled directly from Lie and scalar
radius residuals. The radius floor and inverse-radius branch are consequences
of bounds on the proposed candidate, not assumptions about an unknown true
orbit. Time-dependent bounds can be substituted at each time; no uniform
worst-case disturbance is required by these theorems.
-/
noncomputable section
namespace GNC.LieRadiusDefect
open Matrix Real Gravity LieRadiusApproximation

/-- Error in the polynomial squared-radius approximation is charged once in
the linear residual and again where the nonlinear products require it. -/
theorem approximate_constraint_bound {s shat h U H E C : ℝ}
    (hs : |shat|≤U) (he : |s-shat|≤E) (hh : |h|≤H)
    (hc : |shat+2*h|≤C) :
    |(1+s)*(1+h)^2-1|≤C+E+H^2+2*(U+E)*H+(U+E)*H^2 := by
  have hsu : |s|≤U+E := by
    have ha := abs_sub_le s shat 0
    simp only [sub_zero] at ha
    linarith
  have hsc : |s+2*h|≤C+E := by
    have heq : s+2*h=(shat+2*h)+(s-shat) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add hc he)
  exact (radius_constraint_bound hsu hh).trans (by linarith)

/-- Nonexpansiveness of J gives both radius bounds directly. -/
theorem candidate_radius_bounds (q φ ρ : Vec3) {P : ℝ}
    (hφ : enorm φ<2*π) (hρ : enorm ρ≤P) :
    enorm q-P≤enorm (q+Jacobian.leftAt φ ρ) ∧
      enorm (q+Jacobian.leftAt φ ρ)≤enorm q+P := by
  have hd := (leftAt_nonexpansive φ ρ hφ).trans hρ
  constructor
  · have ht := enorm_add_le (q+Jacobian.leftAt φ ρ) (-Jacobian.leftAt φ ρ)
    rw [add_neg_cancel_right,enorm_neg] at ht
    linarith
  · exact (enorm_add_le _ _).trans (add_le_add le_rfl hd)

theorem inverse_radius_branch {r h H : ℝ} (hr : 0<r)
    (hh : |h|≤H) (hH : H<1) : 0≤(1+h)/r := by
  have hlow := (abs_le.mp hh).1
  apply div_nonneg _ hr.le
  linarith

theorem inverse_cube_linear_bound {h H : ℝ} (hh : |h|≤H) :
    |(1+h)^3-1|≤3*H+3*H^2+H^3 := by
  have hH := (abs_nonneg h).trans hh
  have he : (1+h)^3-1=3*h+3*h^2+h^3 := by ring
  rw [he]
  have ha := (abs_add_le (3*h+3*h^2) (h^3)).trans
    (add_le_add (abs_add_le (3*h) (3*h^2)) le_rfl)
  norm_num only [abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<3)] at ha
  exact ha.trans (by gcongr)

/-- All terms in the complete defect budget. C bounds the polynomial linear
constraint, E its scalar-radius error, and R the polynomial Lie residual.
No number in this expression is an adjustable tolerance. -/
def budget (μ r θ δ P H U E C R B : ℝ) : ℝ :=
  let K := μ/r^3
  let W := (1+|θ|/2+θ^2/12)*r
  let axisError := (|θ|/2+θ^2*(2+δ)/12)*δ*r
  let A := (r+P)*(1+H)/r
  R+K*(3*H^2+H^3)*(P+W)+3*K*H*axisError+|θ| * δ*B+
    K*(3*H+3*H^2+H^3)*(inverseQuadraticBudget |θ| * r)+
    μ*inverseRadiusFactor A/(r-P)^2*(C+E+H^2+2*(U+E)*H+(U+E)*H^2)

/-- A certificate for the full nonlinear inverse-square acceleration defect,
with a polynomial approximate axis, a quadratic approximate inverse Jacobian
and an auxiliary inverse radius. Its hypotheses concern only known candidate
quantities. The positive radius floor and branch are proved within the result.
-/
theorem physical_defect_bound (μ : ℝ) (hμ : 0≤μ)
    (q k khat ρ a b : Vec3) (θ h shat : ℝ)
    (hk : k ⬝ᵥ k=1) (hr : 0<enorm q) (hφ : enorm (θ • k)<2*π)
    {δ P H U E C R B : ℝ} (hδ : enorm (k-khat)≤δ)
    (hρ : enorm ρ≤P) (hP : P<enorm q) (hh : |h|≤H) (hH : H<1)
    (hb : enorm b≤B) (hs : |shat|≤U)
    (he : |(enorm (q+Jacobian.leftAt (θ • k) ρ)^2/enorm q^2-1)-shat|≤E)
    (hc : |shat+2*h|≤C)
    (hR : enorm (a+(μ/enorm q^3) • ρ+(3*(μ/enorm q^3)*h) • ρ-
      (θ • khat) ⨯₃ b+(3*(μ/enorm q^3)*h) • jacobianInverseQuadratic (θ • khat) q)≤R) :
    enorm (field3 μ q+b+Jacobian.leftAt (θ • k) a-
      (field3 μ (q+Jacobian.leftAt (θ • k) ρ)+rotate (rotationExp (θ • k)) b))≤
      budget μ (enorm q) θ δ P H U E C R B := by
  let r := enorm q
  let K := μ/r^3
  let u := (1+h)/r
  let w := jacobianInverseQuadratic (θ • k) q
  let what := jacobianInverseQuadratic (θ • khat) q
  let A := (r+P)*(1+H)/r
  have hP0 := (enorm_nonneg _).trans hρ
  have hH0 := (abs_nonneg _).trans hh
  have hd0 := (enorm_nonneg _).trans hδ
  have hB0 := (enorm_nonneg _).trans hb
  have hK : 0≤K := div_nonneg hμ (pow_nonneg hr.le _)
  have hu : 0≤u := inverse_radius_branch hr hh hH
  have hfloor : 0<r-P := sub_pos.mpr hP
  have hrad := candidate_radius_bounds q (θ • k) ρ hφ hρ
  have hupp : u≤(1+H)/r := by
    apply div_le_div_of_nonneg_right _ hr.le
    linarith [(abs_le.mp hh).2]
  have hA : enorm (q+Jacobian.leftAt (θ • k) ρ)*u≤A := by
    calc
      _ ≤ (r+P)*((1+H)/r) := mul_le_mul hrad.2 hupp hu (by positivity)
      _ = A := by dsimp [A]; ring
  have hA0 : 0≤A := (mul_nonneg (enorm_nonneg _) hu).trans hA
  have hklen := Gravity.unit_enorm k hk
  have hw : enorm w≤(1+|θ|/2+θ^2/12)*r := by
    simpa only [w,r,enorm_smul,hklen,mul_one,sq_abs] using
      jacobianInverseQuadratic_bound (θ • k) q
  have hwe := inverse_axis_error k khat q θ (le_of_eq hklen) hδ
  have hf : enorm (((θ • k)-(θ • khat)) ⨯₃ b)≤|θ| * δ*B := by
    rw [←smul_sub,map_smul,LinearMap.smul_apply,enorm_smul]
    have hhf := (cross_enorm_le (k-khat) b).trans (mul_le_mul hδ hb (enorm_nonneg _) hd0)
    exact (mul_le_mul_of_nonneg_left hhf (abs_nonneg θ)).trans_eq (by ring)
  have hres := inverse_cube_residual_bound a ρ b (θ • k) (θ • khat) w what K h hK
    hR hρ hw hwe hf hh
  have hJ : enorm (q-Jacobian.leftAt (θ • k) w) ≤ inverseQuadraticBudget |θ| * r := by
    have hj := jacobianInverseQuadratic_residual_bound k q hk θ
    have heq : q-Jacobian.leftAt (θ • k) w= -(Jacobian.leftAt (θ • k) w-q) := by module
    rwa [heq,enorm_neg]
  have hgain : |K*((1+h)^3-1)|≤K*(3*H+3*H^2+H^3) := by
    rw [abs_mul,abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left (inverse_cube_linear_bound hh) hK
  have hcub : μ*u^3=K*(1+h)^3 := by dsimp [u,K]; ring
  have hdiff : μ*u^3-radialGain μ q=K*((1+h)^3-1) := by
    rw [hcub]
    change K*(1+h)^3-K=_
    ring
  have hconstraint := approximate_constraint_bound hs he hh hc
  have heq : enorm (q+Jacobian.leftAt (θ • k) ρ)^2*u^2-1=
      (1+(enorm (q+Jacobian.leftAt (θ • k) ρ)^2/r^2-1))*(1+h)^2-1 := by
    dsimp [u]
    ring
  have htotal := Gravity.lie_acceleration_defect_bound μ u hμ (θ • k) q ρ a b w
    hφ hfloor hrad.1 hu hA
  rw [hdiff,hcub,heq] at htotal
  have hfactor : 0≤μ*inverseRadiusFactor A/(r-P)^2 := by
    exact div_nonneg (mul_nonneg hμ (inverseRadiusFactor_nonnegative hA0)) (sq_nonneg _)
  exact htotal.trans (add_le_add (add_le_add hres
    (mul_le_mul hgain hJ (enorm_nonneg _) (by positivity)))
    (mul_le_mul_of_nonneg_left hconstraint hfactor))

end GNC.LieRadiusDefect
