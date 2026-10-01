import GNC.Lie.RotationTaylorBound

/-! Derivative identities from rotational equivariance.

These are first variations of the actual differentiable response, not supplied
Jacobian columns. They let a framed response reconstruct derivatives in the
mean-axis tilt directions without differentiating a frame-selection algorithm.
The response's equivariance and differentiability are explicit hypotheses.
-/
noncomputable section
namespace GNC.EquivariantSensitivity
open Matrix
open scoped Matrix Matrix.Norms.Operator

abbrev Inputs := Fin 4 → Vec3
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def rotateInputs (C : SO3) (z : Inputs) : Inputs := fun i => rotate C (z i)
def orbitDirection (ψ : Vec3) (z : Inputs) : Inputs := fun i => ψ ⨯₃ z i

theorem rotation_curve_derivative (ψ : Vec3) :
    HasDerivAt (fun t : ℝ => (rotationExp (t • ψ)).val) (skew ψ) 0 := by
  simpa [rotationExp, skew_smul] using hasDerivAt_exp_smul_const (skew ψ) (0 : ℝ)

theorem rotated_vector_derivative (ψ x : Vec3) :
    HasDerivAt (fun t : ℝ => rotate (rotationExp (t • ψ)) x) (ψ ⨯₃ x) 0 := by
  have h := SymplecticResponse.mulVec_derivative
    (rotation_curve_derivative ψ) (hasDerivAt_const (0 : ℝ) x)
  simpa [rotate, rotationExp, skew_zero, skew_mulVec] using h

theorem rotated_inputs_derivative (ψ : Vec3) (z : Inputs) :
    HasDerivAt (fun t : ℝ => rotateInputs (rotationExp (t • ψ)) z)
      (orbitDirection ψ z) 0 := by
  exact hasDerivAt_pi.mpr (fun i => rotated_vector_derivative ψ (z i))

/-- The infinitesimal equivariance identity for a vector-valued response. -/
theorem vector_orbit_derivative (Q : Inputs → Vec3) (z : Inputs)
    (D : Inputs →L[ℝ] Vec3)
    (hD : HasFDerivAt Q D z)
    (hQ : ∀ (C : SO3) (x : Inputs), Q (rotateInputs C x) = rotate C (Q x))
    (ψ : Vec3) :
    D (orbitDirection ψ z) = ψ ⨯₃ Q z := by
  have hz : rotateInputs (rotationExp ((0 : ℝ) • ψ)) z = z := by
    ext i j
    simp [rotateInputs, rotationExp, rotate, skew_zero]
  have hD' : HasFDerivAt Q D (rotateInputs (rotationExp ((0 : ℝ) • ψ)) z) := by
    simpa only [hz] using hD
  have h := hD'.comp_hasDerivAt (0 : ℝ) (rotated_inputs_derivative ψ z)
  have he : (fun t : ℝ => Q (rotateInputs (rotationExp (t • ψ)) z)) =
      (fun t : ℝ => rotate (rotationExp (t • ψ)) (Q z)) := by
    funext t
    exact hQ _ _
  dsimp only [Function.comp_def] at h
  rw [he] at h
  exact h.unique (rotated_vector_derivative ψ (Q z))

/-- Changing only the first input is recovered from the output rotation and
three held-input directional derivatives. This identity is the transverse
mean-axis rule; no differentiation of a coordinate-frame selector is needed. -/
theorem vector_first_input (Q : Inputs → Vec3) (z : Inputs)
    (D : Inputs →L[ℝ] Vec3) (hD : HasFDerivAt Q D z)
    (hQ : ∀ (C : SO3) (x : Inputs), Q (rotateInputs C x) = rotate C (Q x))
    (ψ : Vec3) :
    D ![ψ ⨯₃ z 0, 0, 0, 0] = ψ ⨯₃ Q z -
      D ![0, ψ ⨯₃ z 1, ψ ⨯₃ z 2, ψ ⨯₃ z 3] := by
  have he : orbitDirection ψ z = ![ψ ⨯₃ z 0, 0, 0, 0] +
      ![0, ψ ⨯₃ z 1, ψ ⨯₃ z 2, ψ ⨯₃ z 3] := by
    ext i j
    fin_cases i <;> simp [orbitDirection]
  have h := vector_orbit_derivative Q z D hD hQ ψ
  rw [he, map_add] at h
  exact eq_sub_of_add_eq h

/-- The corresponding identity for a matrix response transformed by conjugation. -/
theorem matrix_orbit_derivative (Q : Inputs → Mat3) (z : Inputs)
    (D : Inputs →L[ℝ] Mat3) (hD : HasFDerivAt Q D z)
    (hQ : ∀ (C : SO3) (x : Inputs),
      Q (rotateInputs C x) = C.val * Q x * C⁻¹.val) (ψ : Vec3) :
    D (orbitDirection ψ z) = skew ψ * Q z - Q z * skew ψ := by
  have hz : rotateInputs (rotationExp ((0 : ℝ) • ψ)) z = z := by
    ext i j
    simp [rotateInputs, rotationExp, rotate, skew_zero]
  have hD' : HasFDerivAt Q D (rotateInputs (rotationExp ((0 : ℝ) • ψ)) z) := by
    simpa only [hz] using hD
  have h := hD'.comp_hasDerivAt (0 : ℝ) (rotated_inputs_derivative ψ z)
  have he : (fun t : ℝ => Q (rotateInputs (rotationExp (t • ψ)) z)) =
      (fun t : ℝ => (rotationExp (t • ψ)).val * Q z * (rotationExp (t • ψ))⁻¹.val) := by
    funext t
    exact hQ _ _
  dsimp only [Function.comp_def] at h
  rw [he] at h
  have hi : HasDerivAt (fun t : ℝ => (rotationExp (t • ψ))⁻¹.val) (-skew ψ) 0 := by
    have ht := SymplecticFlow.transpose_derivative (rotation_curve_derivative ψ)
    simpa only [RotationKinematics.inverse_transpose, skew_transpose] using ht
  have hm := SymplecticFlow.mul_derivative
    (SymplecticFlow.mul_derivative (rotation_curve_derivative ψ)
      (hasDerivAt_const (0 : ℝ) (Q z))) hi
  have hd : HasDerivAt
      (fun t : ℝ => (rotationExp (t • ψ)).val * Q z * (rotationExp (t • ψ))⁻¹.val)
      (skew ψ * Q z - Q z * skew ψ) 0 := by
    simpa [rotationExp, skew_zero, RotationKinematics.inverse_transpose,
      sub_eq_add_neg] using hm
  exact h.unique hd

/-- Matrix mean-axis tilt derivative with the other inputs held fixed. -/
theorem matrix_first_input (Q : Inputs → Mat3) (z : Inputs)
    (D : Inputs →L[ℝ] Mat3) (hD : HasFDerivAt Q D z)
    (hQ : ∀ (C : SO3) (x : Inputs),
      Q (rotateInputs C x) = C.val * Q x * C⁻¹.val) (ψ : Vec3) :
    D ![ψ ⨯₃ z 0, 0, 0, 0] = skew ψ * Q z - Q z * skew ψ -
      D ![0, ψ ⨯₃ z 1, ψ ⨯₃ z 2, ψ ⨯₃ z 3] := by
  have he : orbitDirection ψ z = ![ψ ⨯₃ z 0, 0, 0, 0] +
      ![0, ψ ⨯₃ z 1, ψ ⨯₃ z 2, ψ ⨯₃ z 3] := by
    ext i j
    fin_cases i <;> simp [orbitDirection]
  have h := matrix_orbit_derivative Q z D hD hQ ψ
  rw [he, map_add] at h
  exact eq_sub_of_add_eq h

/-- The tilt axis at a nonzero mean rotation along the third coordinate. -/
def transverseTilt (θ dx dy : ℝ) : Vec3 := ![-dy/θ, dx/θ, 0]

theorem transverseTilt_cross {θ : ℝ} (hθ : θ ≠ 0) (dx dy : ℝ) :
    transverseTilt θ dx dy ⨯₃ ![0, 0, θ] = ![dx, dy, 0] := by
  ext i
  fin_cases i <;> simp [transverseTilt, cross_apply] <;> field_simp

/-- Exact first-input derivative for a transverse Cartesian perturbation. -/
theorem vector_transverse (Q : Inputs → Vec3) (z : Inputs)
    (D : Inputs →L[ℝ] Vec3) (hD : HasFDerivAt Q D z)
    (hQ : ∀ (C : SO3) (x : Inputs), Q (rotateInputs C x) = rotate C (Q x))
    {θ : ℝ} (hθ : θ ≠ 0) (hz : z 0 = ![0, 0, θ]) (dx dy : ℝ) :
    D ![![dx, dy, 0], 0, 0, 0] = transverseTilt θ dx dy ⨯₃ Q z -
      D ![0, transverseTilt θ dx dy ⨯₃ z 1,
        transverseTilt θ dx dy ⨯₃ z 2, transverseTilt θ dx dy ⨯₃ z 3] := by
  simpa only [hz, transverseTilt_cross hθ dx dy] using
    vector_first_input Q z D hD hQ (transverseTilt θ dx dy)

/-- Exact matrix counterpart; this supplies the rotation derivative as well. -/
theorem matrix_transverse (Q : Inputs → Mat3) (z : Inputs)
    (D : Inputs →L[ℝ] Mat3) (hD : HasFDerivAt Q D z)
    (hQ : ∀ (C : SO3) (x : Inputs),
      Q (rotateInputs C x) = C.val * Q x * C⁻¹.val)
    {θ : ℝ} (hθ : θ ≠ 0) (hz : z 0 = ![0, 0, θ]) (dx dy : ℝ) :
    D ![![dx, dy, 0], 0, 0, 0] = skew (transverseTilt θ dx dy) * Q z -
      Q z * skew (transverseTilt θ dx dy) -
      D ![0, transverseTilt θ dx dy ⨯₃ z 1,
        transverseTilt θ dx dy ⨯₃ z 2, transverseTilt θ dx dy ⨯₃ z 3] := by
  simpa only [hz, transverseTilt_cross hθ dx dy] using
    matrix_first_input Q z D hD hQ (transverseTilt θ dx dy)

end GNC.EquivariantSensitivity
