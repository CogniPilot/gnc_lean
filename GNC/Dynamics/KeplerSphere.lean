import GNC.Dynamics.GravityField
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The normalized negative-energy Moser map, checked directly.

For mu = 1 and energy -1/2, use ds/dt = 1/|q|. The mapped position
and tangent satisfy X' = U, U' = -X. In dimension three X lies on S^3,
which can be identified with the unit quaternions. This module checks
the sphere constraint, inverse map, reparametrized ODE and exact clock.
It does not formalize SU(2)'s Riemannian metric, uncertain-energy scaling,
global time inversion, or a controlled/thrusting extension.
-/
noncomputable section
open scoped RealInnerProductSpace
namespace GNC.KeplerSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def point (q p : E) : ℝ × E := (1-‖q‖, ‖q‖ • p)
def tangent (q p : E) : ℝ × E :=
  (-⟪q,p⟫, ⟪q,p⟫ • p - (1/‖q‖) • q)

/-- Euclidean sphere identity (not the product's max norm). -/
theorem point_unit (q p : E) (hE : ‖q‖*(‖p‖^2+1)=2) :
    (point q p).1^2 + ‖(point q p).2‖^2 = 1 := by
  simp only [point, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)]
  nlinarith [congrArg (fun a : ℝ => a*‖q‖) hE]

theorem point_tangent_orthogonal (q p : E) (hq : q ≠ 0)
    (hE : ‖q‖*(‖p‖^2+1)=2) :
    (point q p).1*(tangent q p).1 + ⟪(point q p).2,(tangent q p).2⟫ = 0 := by
  have hr : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [point, tangent, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm p q]
  field_simp
  nlinarith [congrArg (fun a : ℝ => a*⟪p,q⟫) hE]

theorem tangent_unit (q p : E) (hq : q ≠ 0) (hE : ‖q‖*(‖p‖^2+1)=2) :
    (tangent q p).1^2 + ‖(tangent q p).2‖^2 = 1 := by
  have hr : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [tangent, neg_sq, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right, real_inner_comm p q]
  field_simp
  nlinarith [congrArg (fun a : ℝ => a*⟪q,p⟫^2*‖q‖) hE]

/-- Away from collision, the lifted position/tangent retain all q,p data. -/
theorem reconstruct (q p : E) (hq : q ≠ 0) :
    (1/(1-(point q p).1)) • (point q p).2 = p ∧
    -(tangent q p).1 • (point q p).2 -
      (1-(point q p).1) • (tangent q p).2 = q := by
  have hr : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  constructor
  · simp [point, smul_smul, hr]
  · simp only [point, tangent, neg_neg, sub_sub_cancel, smul_sub, smul_smul]
    rw [mul_one_div_cancel hr]
    module

/-- A physical Kepler solution with a positive-radius clock has the
regularized equations. Existence/inversion of the clock is not assumed proved. -/
theorem reparametrize {q p : ℝ → E} {clock : ℝ → ℝ} {s : ℝ}
    (hq : HasDerivAt q (p (clock s)) (clock s))
    (hp : HasDerivAt p ((-1/‖q (clock s)‖^3) • q (clock s)) (clock s))
    (ht : HasDerivAt clock ‖q (clock s)‖ s) (hn : q (clock s) ≠ 0) :
    HasDerivAt (q ∘ clock) (‖q (clock s)‖ • p (clock s)) s ∧
    HasDerivAt (p ∘ clock) ((-1/‖q (clock s)‖^2) • q (clock s)) s := by
  refine ⟨hq.scomp s ht, ?_⟩
  convert hp.scomp s ht using 1
  rw [smul_smul]
  congr 1
  have hr : ‖q (clock s)‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  field_simp

/-- The physical inverse-square dynamics become an exact oscillator,
on the normalized energy shell and in regularized time. -/
theorem oscillator {q p : ℝ → E} {s : ℝ}
    (hq : HasDerivAt q (‖q s‖ • p s) s)
    (hp : HasDerivAt p ((-1/‖q s‖^2) • q s) s)
    (hn : q s ≠ 0) (hE : ‖q s‖*(‖p s‖^2+1)=2) :
    HasDerivAt (fun t => point (q t) (p t)) (tangent (q s) (p s)) s ∧
    HasDerivAt (fun t => tangent (q t) (p t)) (-(point (q s) (p s))) s := by
  have hr : ‖q s‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hd := Gravity.norm_derivative hq hn
  simp only [real_inner_smul_right, mul_div_cancel_left₀ _ hr] at hd
  have hc : HasDerivAt (fun t => ⟪q t,p t⟫) (1-‖q s‖) s := by
    convert hq.inner ℝ hp using 1
    simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    nlinarith [congrArg (fun a : ℝ => a*‖q s‖^2) hE]
  have hi : HasDerivAt (fun t => 1/‖q t‖)
      (-⟪q s,p s⟫/‖q s‖^2) s := by
    simpa only [one_div] using hd.inv hr
  have hscale : ‖q s‖*(-1/‖q s‖^2) = -(1/‖q s‖) := by field_simp
  have hcancel : ⟪q s,p s⟫*(-1/‖q s‖^2) = -⟪q s,p s⟫/‖q s‖^2 := by ring
  have hprod : (1/‖q s‖)*‖q s‖ = 1 := by field_simp
  constructor
  · convert (hd.const_sub 1).prodMk (hd.smul hp) using 1
    simp only [point, tangent, smul_smul, hscale]
    congr 1
    module
  · convert hc.neg.prodMk ((hc.smul hp).sub (hi.smul hq)) using 1
    simp only [point, tangent, Prod.neg_mk, smul_smul, hcancel, hprod, one_smul]
    congr 1
    module

/-- Explicit solution of the lifted oscillator. -/
def greatCircle (X U : ℝ × E) (s : ℝ) : ℝ × E :=
  Real.cos s • X + Real.sin s • U
def greatTangent (X U : ℝ × E) (s : ℝ) : ℝ × E :=
  -Real.sin s • X + Real.cos s • U

theorem greatCircle_initial (X U : ℝ × E) :
    greatCircle X U 0 = X ∧ greatTangent X U 0 = U := by
  simp [greatCircle, greatTangent]

theorem greatCircle_derivative (X U : ℝ × E) (s : ℝ) :
    HasDerivAt (greatCircle X U) (greatTangent X U s) s := by
  simpa [greatCircle, greatTangent] using
    ((Real.hasDerivAt_cos s).smul_const X).add ((Real.hasDerivAt_sin s).smul_const U)

theorem greatTangent_derivative (X U : ℝ × E) (s : ℝ) :
    HasDerivAt (greatTangent X U) (-(greatCircle X U s)) s := by
  convert ((Real.hasDerivAt_sin s).neg.smul_const X).add
    ((Real.hasDerivAt_cos s).smul_const U) using 1
  simp [greatTangent, greatCircle, neg_smul, add_comm]

/-- The phase correction underlying the normalized Ligon--Schaaf map:
an oscillator of instantaneous rate k becomes one of rate k + phi'.
This is an ODE identity, not a global symplectomorphism theorem. -/
theorem phase_correction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X U : ℝ → F} {phi : ℝ → ℝ} {t k a : ℝ}
    (hX : HasDerivAt X (k • U t) t)
    (hU : HasDerivAt U ((-k) • X t) t)
    (hphi : HasDerivAt phi a t) :
    HasDerivAt (fun s => Real.cos (phi s) • X s + Real.sin (phi s) • U s)
      ((k+a) • (-Real.sin (phi t) • X t + Real.cos (phi t) • U t)) t ∧
    HasDerivAt (fun s => -Real.sin (phi s) • X s + Real.cos (phi s) • U s)
      ((-(k+a)) • (Real.cos (phi t) • X t + Real.sin (phi t) • U t)) t := by
  constructor
  · convert (hphi.cos.smul hX).add (hphi.sin.smul hU) using 1 <;> module
  · convert (hphi.sin.neg.smul hX).add (hphi.cos.smul hU) using 1 <;>
      simp only [Pi.neg_apply] <;> module

/-- Along the regularized Kepler solution, the phase -q.p makes the
oscillator rate equal dt/ds = radius. Thus it removes the variable rate
when expressed in physical time. The global inverse remains separate. -/
theorem ligonSchaaf_regularized {q p : ℝ → E} {s : ℝ}
    (hq : HasDerivAt q (‖q s‖ • p s) s)
    (hp : HasDerivAt p ((-1/‖q s‖^2) • q s) s)
    (hn : q s ≠ 0) (hE : ‖q s‖*(‖p s‖^2+1)=2) :
    HasDerivAt
      (fun t => greatCircle (point (q t) (p t)) (tangent (q t) (p t)) (-⟪q t,p t⟫))
      (‖q s‖ • greatTangent (point (q s) (p s)) (tangent (q s) (p s)) (-⟪q s,p s⟫)) s ∧
    HasDerivAt
      (fun t => greatTangent (point (q t) (p t)) (tangent (q t) (p t)) (-⟪q t,p t⟫))
      ((-‖q s‖) • greatCircle (point (q s) (p s)) (tangent (q s) (p s)) (-⟪q s,p s⟫)) s := by
  have hr : ‖q s‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hc : HasDerivAt (fun t => ⟪q t,p t⟫) (1-‖q s‖) s := by
    convert hq.inner ℝ hp using 1
    simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    nlinarith [congrArg (fun a : ℝ => a*‖q s‖^2) hE]
  obtain ⟨hX, hU⟩ := oscillator hq hp hn hE
  have hX' : HasDerivAt (fun t => point (q t) (p t))
      ((1 : ℝ) • tangent (q s) (p s)) s := by simpa using hX
  have hU' : HasDerivAt (fun t => tangent (q t) (p t))
      ((-1 : ℝ) • point (q s) (p s)) s := by simpa using hU
  simpa only [greatCircle, greatTangent, sub_neg_eq_add, add_sub_cancel,
    neg_sub, add_sub_cancel_left] using phase_correction (k := 1) hX' hU' hc.neg

/-- The lifted oscillator preserves its Euclidean phase-space norm.
Applied to differences, this gives exact uncertainty preservation at a
common oscillator time, before nonlinear physical reconstruction. -/
theorem oscillator_norm_preserved (X U : E) (s : ℝ) :
    ‖Real.cos s • X + Real.sin s • U‖^2 +
      ‖-Real.sin s • X + Real.cos s • U‖^2 = ‖X‖^2 + ‖U‖^2 := by
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right, neg_sq]
  nlinarith [congrArg (fun a : ℝ => a*‖X‖^2) (Real.sin_sq_add_cos_sq s),
    congrArg (fun a : ℝ => a*‖U‖^2) (Real.sin_sq_add_cos_sq s)]

/-- Exact physical-time quadrature. Solving for s at a requested t is
still a separate inverse problem, with positivity supplied by the radius. -/
def physicalClock (X U : ℝ × E) (s : ℝ) : ℝ :=
  s-X.1*Real.sin s-U.1*(1-Real.cos s)

theorem physicalClock_derivative (X U : ℝ × E) (s : ℝ) :
    HasDerivAt (physicalClock X U) (1-(greatCircle X U s).1) s := by
  convert ((hasDerivAt_id s).sub ((Real.hasDerivAt_sin s).const_mul X.1)).sub
    (((Real.hasDerivAt_cos s).const_sub 1).const_mul U.1) using 1
  simp [physicalClock, greatCircle, smul_eq_mul]
  ring

theorem physicalClock_initial (X U : ℝ × E) : physicalClock X U 0 = 0 := by
  simp [physicalClock]

end GNC.KeplerSphere
