import GNC.Dynamics.GravityReferenceDefect
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Nonlinear Magnus brackets retain derivatives of the physical field.
We use the negative of mathlib's vector-field bracket, so a linear field
Ax has the matrix convention [A,B]=AB-BA. The corresponding left-flow
Magnus integrands have the usual matrix signs. No convergence or numerical
remainder is inferred from these finite differential identities.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.NonlinearGravityMagnus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def field (g : E → E) (a : E) (x : E × E) : E × E := (x.2,g x.1+a)
def bracket (f g : (E × E) → E × E) : (E × E) → E × E :=
  VectorField.lieBracket ℝ g f

theorem field_fderiv {g : E → E} {G : E →L[ℝ] E} (a : E) (x : E × E)
    (hg : HasFDerivAt g G x.1) :
    HasFDerivAt (field g a)
      ((ContinuousLinearMap.snd ℝ E E).prod (G.comp (ContinuousLinearMap.fst ℝ E E))) x := by
  exact (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.prodMk
    ((hg.comp x (ContinuousLinearMap.fst ℝ E E).hasFDerivAt).add_const a)

/-- Gravity cancels from the pair bracket of two different prescribed
inertial accelerations. The result is a pure position translation. -/
theorem sampled_bracket {g : E → E} {G : E →L[ℝ] E}
    (a b : E) (x : E × E) (hg : HasFDerivAt g G x.1) :
    bracket (field g a) (field g b) x = (b-a,0) := by
  simp [bracket, VectorField.lieBracket, (field_fderiv a x hg).fderiv,
    (field_fderiv b x hg).fderiv, field, Prod.sub_def]

/-- The next bracket differentiates the spatial gravity coefficient. -/
theorem bracket_position {g : E → E} {G : E →L[ℝ] E}
    (a c : E) (x : E × E) (hg : HasFDerivAt g G x.1) :
    bracket (field g a) (fun _ => (c,0)) x = (0,G c) := by
  simp [bracket, VectorField.lieBracket, (field_fderiv a x hg).fderiv,
    fderiv_const, field]

/-- A further bracket contains a spatial second derivative. Finite matrix
commutators evaluated at a state would miss this term. -/
theorem bracket_gradient {g h : E → E} {G H : E →L[ℝ] E}
    (a : E) (x : E × E) (hg : HasFDerivAt g G x.1) (hh : HasFDerivAt h H x.1) :
    bracket (field g a) (fun z => (0,h z.1)) x = (h x.1,-H x.2) := by
  have hd : HasFDerivAt (fun z : E × E => ((0:E),h z.1))
      ((0 : (E × E) →L[ℝ] E).prod (H.comp (ContinuousLinearMap.fst ℝ E E))) x :=
    (hasFDerivAt_const (0:E) x).prodMk (hh.comp x (ContinuousLinearMap.fst ℝ E E).hasFDerivAt)
  simp [bracket, VectorField.lieBracket, (field_fderiv a x hg).fderiv, hd.fderiv, field]

/-- Exact conjugacy of the first-two-term nonlinear Magnus vector field to
a constant-acceleration gravity problem. If g is inverse-square, the inner
problem is Stark. This solves the retained exponent, not the varying-input
physical ODE; omitted Magnus terms still require error bounds. -/
theorem shifted_stark_derivative (g : E → E) (a c : E) {h s : ℝ} (hh : h ≠ 0)
    {q v : ℝ → E}
    (hq : HasDerivAt q (h • v s) s)
    (hv : HasDerivAt v (h • (g (q s)+a)) s) :
    HasDerivAt (fun t => (q t,v t-h⁻¹ • c))
      (h • (v s-h⁻¹ • c)+c,h • (g (q s)+a)) s := by
  convert hq.prodMk (hv.sub_const (h⁻¹ • c)) using 1
  simp [smul_sub, smul_smul, hh]

section Physical
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem gravity_differentiable (μ : ℝ) (q : F) (hq : q ≠ 0) :
    DifferentiableAt ℝ (Gravity.field μ) q := by
  unfold Gravity.field
  have hc : DifferentiableAt ℝ (fun _ : F => -μ) q := differentiableAt_const _
  have hn : DifferentiableAt ℝ (fun x : F => ‖x‖^3) q :=
    ((differentiableAt_id : DifferentiableAt ℝ (fun x : F => x) q).norm ℝ hq).pow 3
  simpa only [div_eq_mul_inv] using
    (hc.mul (hn.inv (pow_ne_zero 3 (norm_ne_zero_iff.mpr hq)))).smul differentiableAt_id

/-- Connect the vector-field Frechet derivative to the already proved
physical gravity derivative, rather than postulating a linearization. -/
theorem gravity_fderiv (μ : ℝ) (q v : F) (hq : q ≠ 0) :
    fderiv ℝ (Gravity.field μ) q v = Gravity.gradient μ q v := by
  have hp : HasDerivAt (fun t : ℝ => q+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add q
  have hq0 : q+(0:ℝ) • v ≠ 0 := by simpa using hq
  have hF : HasFDerivAt (Gravity.field μ) (fderiv ℝ (Gravity.field μ) q)
      (q+(0:ℝ) • v) := by simpa using (gravity_differentiable μ q hq).hasFDerivAt
  have h1 := hF.comp_hasDerivAt 0 hp
  have h2 := Gravity.field_derivative μ (f := fun t : ℝ => q+t • v) hp hq0
  simpa using h1.unique h2

theorem physical_sampled_bracket (μ : ℝ) (a b q v : F) (hq : q ≠ 0) :
    bracket (field (Gravity.field μ) a) (field (Gravity.field μ) b) (q,v) = (b-a,0) :=
  sampled_bracket a b (q,v) (gravity_differentiable μ q hq).hasFDerivAt

theorem physical_bracket_position (μ : ℝ) (a c q v : F) (hq : q ≠ 0) :
    bracket (field (Gravity.field μ) a) (fun _ => (c,0)) (q,v) =
      (0,Gravity.gradient μ q c) := by
  rw [bracket_position a c (q,v) (gravity_differentiable μ q hq).hasFDerivAt,
    gravity_fderiv μ q c hq]

end Physical

/-- Spatial derivative coefficients on the positive radial ray. -/
def radialCoefficient (μ : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (-1:ℝ)^(n+1)*((n+1).factorial:ℝ)*μ/r^(n+2)

theorem radialCoefficient_derivative (μ : ℝ) (n : ℕ) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (radialCoefficient μ n) (radialCoefficient μ (n+1) r) r := by
  have h := (hasDerivAt_const r ((-1:ℝ)^(n+1)*((n+1).factorial:ℝ)*μ)).div
    ((hasDerivAt_id r).pow (n+2)) (pow_ne_zero _ hr)
  convert h using 1
  dsimp [radialCoefficient]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [pow_succ]
  field_simp
  ring

/-- Every repeated radial derivative is nonzero. Thus the physical
gravity dependence cannot disappear after a fixed number of spatial
derivatives, even though the sampled 5x5 gravity matrices are nilpotent. -/
theorem radialCoefficient_ne_zero {μ r : ℝ} (hμ : μ ≠ 0) (hr : r ≠ 0) (n : ℕ) :
    radialCoefficient μ n r ≠ 0 := by
  unfold radialCoefficient
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (by exact_mod_cast Nat.factorial_ne_zero (n+1))) hμ) (pow_ne_zero _ hr)

theorem radial_iteratedDeriv (μ : ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    iteratedDeriv n (fun s : ℝ => -μ/s^2) r = radialCoefficient μ n r := by
  induction n generalizing r with
  | zero => simp [radialCoefficient]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun s : ℝ => -μ/s^2) =ᶠ[nhds r]
        radialCoefficient μ n := by
      filter_upwards [Ioi_mem_nhds hr] with s hs
      exact ih hs
    exact ((radialCoefficient_derivative μ n r hr.ne').congr_of_eventuallyEq he).deriv

end GNC.NonlinearGravityMagnus
