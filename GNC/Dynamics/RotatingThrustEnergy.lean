import GNC.Dynamics.OrbitalEnergy

/-! Exact Jacobi energy for inverse-square gravity and a constant thrust
vector in a uniformly rotating reference frame. No linearization occurs.
The skewness condition is the defining inner-product property of rotation. -/
noncomputable section
namespace GNC.RotatingThrust
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def field (mu : ℝ) (W : E →L[ℝ] E) (a q v : E) : E :=
  Gravity.field mu q+a-(2:ℝ) • W v-W (W q)

def jacobiEnergy (mu : ℝ) (W : E →L[ℝ] E) (a q v : E) : ℝ :=
  OrbitalEnergy.specificEnergy mu q v-⟪a,q⟫-‖W q‖^2/2

theorem jacobiEnergy_derivative (W : E →L[ℝ] E)
    (hW : ∀ x y, ⟪W x,y⟫ = -⟪x,W y⟫)
    {q v : ℝ → E} {mu t : ℝ} {a : E}
    (hq : HasDerivAt q (v t) t)
    (hv : HasDerivAt v (field mu W a (q t) (v t)) t)
    (hz : q t ≠ 0) :
    HasDerivAt (fun s => jacobiEnergy mu W a (q s) (v s)) 0 t := by
  have hv' : HasDerivAt v
      (Gravity.field mu (q t)+(a-(2:ℝ) • W (v t)-W (W (q t)))) t := by
    simpa [field, sub_eq_add_neg, add_assoc] using hv
  have hs : ⟪v t,W (v t)⟫ = 0 := by
    have h := hW (v t) (v t)
    rw [real_inner_comm] at h
    linarith
  have hc := hW (v t) (W (q t))
  convert ((OrbitalEnergy.energy_derivative hq hv' hz).sub
    ((hasDerivAt_const t a).inner ℝ hq)).sub
      ((W.hasFDerivAt.comp_hasDerivAt t hq).norm_sq.div_const 2) using 1
  simp only [inner_sub_right, inner_smul_right, inner_zero_left, Function.comp_apply, hs]
  rw [real_inner_comm a (v t), real_inner_comm (W (v t)) (W (q t))]
  linarith

/-- The same integral in canonical momentum p=v+Wq. This is the rotating
Kepler Hamiltonian plus the constant-force potential. -/
theorem canonical_energy (mu : ℝ) (W : E →L[ℝ] E) (a q v : E) :
    jacobiEnergy mu W a q v =
      ‖v+W q‖^2/2-mu/‖q‖-⟪v+W q,W q⟫-⟪a,q⟫ := by
  simp only [jacobiEnergy, OrbitalEnergy.specificEnergy, norm_add_sq_real,
    inner_add_left, real_inner_self_eq_norm_sq]
  ring

/-- The planar angular-momentum rate under constant reference-frame force;
the central-gravity and rotation contributions cancel, but the force torque
generally does not. Here k=mu/r^3 is allowed to depend on the state. -/
theorem angular_momentum_rate (k w x y px py ax ay : ℝ) :
    (px+w*y)*py+x*(-k*y+ay-w*px) -
      (py-w*x)*px-y*(-k*x+ax+w*py) = x*ay-y*ax := by ring

end GNC.RotatingThrust
