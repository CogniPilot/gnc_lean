import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Tactic

/-! The reduced two-frame group is mathlib's semidirect product.
Its natural discrete dynamics are an endomorphism between two translations.
This proves exact error propagation before any linearization or filtering.
-/
noncomputable section
namespace GNC.TwoFrame

section Affine
variable {H : Type*} [Group H]

def DiscreteGroupAffine (f : H → H) : Prop :=
  ∀ X Y, f (X*Y) = f X*(f 1)⁻¹*f Y

theorem translated_hom_affine (ψ : H →* H) (L R : H) :
    DiscreteGroupAffine (fun X => L*ψ X*R) := by
  intro X Y
  simp only [map_mul, map_one, mul_one]
  group

theorem translated_hom_error (ψ : H →* H) (L R X H₀ : H) :
    (L*ψ H₀*R)⁻¹*(L*ψ X*R) = R⁻¹*ψ (H₀⁻¹*X)*R := by
  simp only [map_mul, map_inv]
  group

/-- A deterministic update has an exact error identity for any correction,
including an exponential correction chosen from an innovation. -/
theorem correction_error (X H₀ C : H) :
    (H₀*C)⁻¹*X = C⁻¹*(H₀⁻¹*X) := by group

end Affine

section Semidirect
variable {N G : Type*} [Group N] [Group G] (φ : G →* MulAut N)

def liftEndomorphism (F : N →* N)
    (hF : ∀ g x, F (φ g x) = φ g (F x)) :
    (N ⋊[φ] G) →* (N ⋊[φ] G) where
  toFun X := ⟨F X.left, X.right⟩
  map_one' := by ext <;> simp
  map_mul' X Y := by
    ext <;> simp [hF]

def naturalStep (F : N →* N)
    (hF : ∀ g x, F (φ g x) = φ g (F x))
    (d : N) (U X : N ⋊[φ] G) : N ⋊[φ] G :=
  SemidirectProduct.inl d * liftEndomorphism φ F hF X * U

theorem naturalStep_coordinates (F : N →* N)
    (hF : ∀ g x, F (φ g x) = φ g (F x))
    (d : N) (U X : N ⋊[φ] G) :
    naturalStep φ F hF d U X =
      ⟨d*F X.left*φ X.right U.left, X.right*U.right⟩ := by
  ext <;> simp [naturalStep, liftEndomorphism]

theorem naturalStep_affine (F : N →* N)
    (hF : ∀ g x, F (φ g x) = φ g (F x)) (d : N) (U : N ⋊[φ] G) :
    DiscreteGroupAffine (naturalStep φ F hF d U) :=
  translated_hom_affine _ _ _

theorem naturalStep_error (F : N →* N)
    (hF : ∀ g x, F (φ g x) = φ g (F x))
    (d : N) (U X H₀ : N ⋊[φ] G) :
    (naturalStep φ F hF d U H₀)⁻¹ * naturalStep φ F hF d U X =
      U⁻¹*liftEndomorphism φ F hF (H₀⁻¹*X)*U :=
  translated_hom_error _ _ _ _ _

/-- The full translation output is equivariant under the affine action.
Component extraction follows whenever the action preserves those components. -/
theorem output_compatible (X Y : N ⋊[φ] G) :
    (X*Y).left = X.left*φ X.right Y.left := rfl

theorem innovation_eq_error (X H₀ : N ⋊[φ] G) :
    φ H₀.right⁻¹ (H₀.left⁻¹*X.left) = (H₀⁻¹*X).left := by
  simp [map_mul]

end Semidirect

section LinearAction
variable {G E : Type*} [Group G] [AddCommGroup E] [Module ℝ E]

/-- A linear group action supplies the automorphisms required by mathlib's
semidirect product. In particular it can be a rotation-and-scale action. -/
def additiveAction (ρ : G →* E ≃ₗ[ℝ] E) : G →* MulAut (Multiplicative E) where
  toFun g := (ρ g).toAddEquiv.toMultiplicative
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

abbrev Space (ρ : G →* E ≃ₗ[ℝ] E) := Multiplicative E ⋊[additiveAction ρ] G

def linearStep (ρ : G →* E ≃ₗ[ℝ] E) (F : E →ₗ[ℝ] E)
    (hF : ∀ g x, F (ρ g x) = ρ g (F x)) (d u : E) (Ω : G)
    (X : Space ρ) : Space ρ :=
  naturalStep (additiveAction ρ) F.toAddMonoidHom.toMultiplicative
    (fun g x => hF g x.toAdd) (Multiplicative.ofAdd d)
    ⟨Multiplicative.ofAdd u, Ω⟩ X

theorem linearStep_coordinates (ρ : G →* E ≃ₗ[ℝ] E) (F : E →ₗ[ℝ] E)
    (hF : ∀ g x, F (ρ g x) = ρ g (F x)) (d u : E) (Ω g : G) (x : E) :
    linearStep ρ F hF d u Ω ⟨Multiplicative.ofAdd x,g⟩ =
      ⟨Multiplicative.ofAdd (F x+d+ρ g u), g*Ω⟩ := by
  rw [linearStep, naturalStep_coordinates]
  congr 1
  change d+F x+ρ g u = F x+d+ρ g u
  abel

theorem linearStep_affine (ρ : G →* E ≃ₗ[ℝ] E) (F : E →ₗ[ℝ] E)
    (hF : ∀ g x, F (ρ g x) = ρ g (F x)) (d u : E) (Ω : G) :
    DiscreteGroupAffine (linearStep ρ F hF d u Ω) :=
  naturalStep_affine _ _ _ _ _

theorem innovation_noise (ρ : G →* E ≃ₗ[ℝ] E) (g : G) (x h w : E) :
    ρ g⁻¹ (x+w-h) = ρ g⁻¹ (x-h)+ρ g⁻¹ w := by
  simp only [map_sub, map_add]
  abel

theorem component_output_compatible {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ρ : G →* E ≃ₗ[ℝ] E) (σ : G →* V ≃ₗ[ℝ] V) (P : E →ₗ[ℝ] V)
    (hP : ∀ g x, P (ρ g x) = σ g (P x)) (X Y : Space ρ) :
    P (X*Y).left.toAdd = P X.left.toAdd+σ X.right (P Y.left.toAdd) := by
  change P (X.left.toAdd+ρ X.right Y.left.toAdd) = _
  rw [map_add, hP]

/-- Arbitrary nonzero scales can be combined with a linear representation.
Restricting the scalar factor to positive units gives the paper's scale group. -/
def scaledLinearEquiv (s : ℝˣ) (R : E ≃ₗ[ℝ] E) : E ≃ₗ[ℝ] E where
  toFun x := s.val • R x
  invFun x := (s⁻¹).val • R.symm x
  left_inv x := by simp [map_smul, smul_smul]
  right_inv x := by simp [map_smul, smul_smul]
  map_add' x y := by simp [smul_add]
  map_smul' r x := by simp [map_smul, smul_smul, mul_comm]

def scaledRepresentation (ρ : G →* E ≃ₗ[ℝ] E) : (ℝˣ × G) →* E ≃ₗ[ℝ] E where
  toFun p := scaledLinearEquiv p.1 (ρ p.2)
  map_one' := by ext x; simp [scaledLinearEquiv]
  map_mul' p q := by ext x; simp [scaledLinearEquiv, map_smul, smul_smul, mul_comm]

theorem scaled_action (ρ : G →* E ≃ₗ[ℝ] E) (s : ℝˣ) (g : G) (x : E) :
    scaledRepresentation ρ (s,g) x = s.val • ρ g x := rfl

/-- The velocity/position integrator commutes with every common linear
action on the two vectors, including arbitrary spatial rotations and scales. -/
theorem integration_commutes (R : E →ₗ[ℝ] E) (dt : ℝ) (v p : E) :
    (R v, R p+dt • R v) = (R v, R (p+dt • v)) := by simp

def pairRepresentation (ρ : G →* E ≃ₗ[ℝ] E) : G →* (E × E) ≃ₗ[ℝ] (E × E) where
  toFun g := (ρ g).prodCongr (ρ g)
  map_one' := by ext x <;> simp
  map_mul' g h := by ext x <;> simp

def integrator (dt : ℝ) : (E × E) →ₗ[ℝ] (E × E) where
  toFun x := (x.1, x.2+dt • x.1)
  map_add' x y := by ext <;> simp [smul_add] <;> abel
  map_smul' r x := by ext <;> simp [smul_add, smul_smul, mul_comm]

theorem integrator_commutes_scaled (ρ : G →* E ≃ₗ[ℝ] E) (dt : ℝ)
    (g : ℝˣ × G) (x : E × E) :
    integrator dt (scaledRepresentation (pairRepresentation ρ) g x) =
      scaledRepresentation (pairRepresentation ρ) g (integrator dt x) := by
  ext <;> simp [integrator, scaledRepresentation, scaledLinearEquiv,
    pairRepresentation, map_add, map_smul, smul_add, smul_smul, mul_comm]

/-- Scaled odometry is a special case of the actual semidirect group
construction, not just a formal similarity of coordinate equations. -/
theorem scaled_odometry_affine (ρ : G →* E ≃ₗ[ℝ] E) (u : E) (Ω : G) :
    DiscreteGroupAffine (linearStep (scaledRepresentation ρ) LinearMap.id
      (fun _ _ => rfl) 0 u (1,Ω)) := linearStep_affine _ _ _ _ _ _

/-- Scaled velocity/position propagation with arbitrary common linear
actions, known additive acceleration d, and arbitrary step dt. -/
theorem scaled_inertial_affine (ρ : G →* E ≃ₗ[ℝ] E)
    (dt : ℝ) (d u : E) (Ω : G) :
    DiscreteGroupAffine (linearStep (scaledRepresentation (pairRepresentation ρ))
      (integrator dt) (integrator_commutes_scaled ρ dt) (d,0) (u,0) (1,Ω)) :=
  linearStep_affine _ _ _ _ _ _

end LinearAction
end GNC.TwoFrame
