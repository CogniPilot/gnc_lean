import GNC.Analysis.SymplecticResponse

/-! The integral response itself solves the forced matrix equation.
Only the mission interval needs the fundamental-matrix ODE and symplectic
identity; continuity suffices elsewhere for the integral primitive.
-/
noncomputable section
namespace GNC.SymplecticResponse
open Matrix
open scoped Matrix Matrix.Norms.Elementwise
set_option autoImplicit false
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem right_inverse (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ) {T : ℝ}
    (hJ : J*J = -1)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt F (A t*F t) t)
    (hA : ∀ t ∈ Set.Icc (0:ℝ) T, (A t)ᵀ*J+J*A t = 0)
    (hi : F 0 = 1) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    F t*pullback J (F t) = 1 := by
  have hp := SymplecticFlow.preserves_form F A J hd hA hi t ht
  apply mul_eq_one_comm.mp
  change (-J)*(F t)ᵀ*J*F t = 1
  calc
    _ = (-J)*((F t)ᵀ*J*F t) := by noncomm_ring
    _ = 1 := by
      rw [hp,neg_mul,hJ]
      ext i j
      exact neg_neg ((1 : Matrix n n ℝ) i j)

def forced (F : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ) (u : ℝ → n → ℝ) (t : ℝ) : n → ℝ :=
  F t *ᵥ (∫ s in (0:ℝ)..t, pullback J (F s) *ᵥ u s)

omit [DecidableEq n] in
theorem forced_initial (F : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ) (u : ℝ → n → ℝ) :
    forced F J u 0 = 0 := by simp [forced]

omit [DecidableEq n] in
theorem integrand_continuous (F : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (u : ℝ → n → ℝ) (hF : Continuous F) (hu : Continuous u) :
    Continuous (fun s => pullback J (F s) *ᵥ u s) :=
  ((continuous_const.matrix_mul hF.matrix_transpose).matrix_mul continuous_const).matrix_mulVec hu

omit [DecidableEq n] in
theorem primitive_derivative (F : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (u : ℝ → n → ℝ) (hF : Continuous F) (hu : Continuous u) (t : ℝ) :
    HasDerivAt (fun t => ∫ s in (0:ℝ)..t, pullback J (F s) *ᵥ u s)
      (pullback J (F t) *ᵥ u t) t := by
  have hc := integrand_continuous F J u hF hu
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

omit [DecidableEq n] in
theorem forced_continuous (F : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (u : ℝ → n → ℝ) (hF : Continuous F) (hu : Continuous u) :
    Continuous (forced F J u) :=
  hF.matrix_mulVec (continuous_iff_continuousAt.mpr
    (fun t => (primitive_derivative F J u hF hu t).continuousAt))

theorem forced_derivative (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (u : ℝ → n → ℝ) {T : ℝ} (hF : Continuous F) (hu : Continuous u)
    (hJ : J*J = -1)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt F (A t*F t) t)
    (hA : ∀ t ∈ Set.Icc (0:ℝ) T, (A t)ᵀ*J+J*A t = 0)
    (hi : F 0 = 1) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    HasDerivAt (forced F J u) (A t *ᵥ forced F J u t+u t) t := by
  have h := mulVec_derivative (hd t ht) (primitive_derivative F J u hF hu t)
  have hinv := right_inverse F A J hJ hd hA hi ht
  simpa only [forced,mulVec_mulVec,hinv,one_mulVec] using h

end GNC.SymplecticResponse
