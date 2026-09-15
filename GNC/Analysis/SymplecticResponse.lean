import GNC.Analysis.SymplecticFlow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Finite-horizon variation of constants for symplectic matrix flows.
The inverse and its derivative follow from the actual fundamental-matrix
ODE. Only the prescribed horizon is used; no global extension is assumed.
-/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Elementwise
namespace GNC.SymplecticResponse
variable {n : Type*} [Fintype n] [DecidableEq n]

def pullback (J F : Matrix n n ℝ) : Matrix n n ℝ := (-J)*Fᵀ*J

theorem pullback_derivative {F : ℝ → Matrix n n ℝ} {A J : Matrix n n ℝ} {t : ℝ}
    (hF : HasDerivAt F (A*F t) t) (hA : Aᵀ*J+J*A = 0) :
    HasDerivAt (fun s => pullback J (F s)) (-(pullback J (F t)*A)) t := by
  have h := SymplecticFlow.mul_derivative
    (SymplecticFlow.mul_derivative (hasDerivAt_const t (-J))
      (SymplecticFlow.transpose_derivative hF)) (hasDerivAt_const t J)
  have ha : Aᵀ*J = -(J*A) := eq_neg_of_add_eq_zero_left hA
  convert h using 1
  simp only [zero_mul, zero_add, mul_zero, add_zero, transpose_mul]
  change -(pullback J (F t)*A) = (-J)*((F t)ᵀ*Aᵀ)*J
  rw [Matrix.mul_assoc (-J), Matrix.mul_assoc (F t)ᵀ, ha]
  unfold pullback
  noncomm_ring

omit [DecidableEq n] in
theorem mulVec_derivative {F : ℝ → Matrix n n ℝ} {x : ℝ → n → ℝ}
    {D : Matrix n n ℝ} {v : n → ℝ} {t : ℝ}
    (hF : HasDerivAt F D t) (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => F s *ᵥ x s) (D *ᵥ x t+F t *ᵥ v) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hF i) j).mul (hasDerivAt_pi.mp hx j))
  convert h using 1 <;> simp [mulVec, dotProduct, Finset.sum_add_distrib]
  funext s
  simp

/-- The forcing is pulled back before integration; its sign and time
variation are retained exactly. This is an identity for an existing solution
of the forced linear equation, not an approximation to nonlinear motion. -/
theorem endpoint (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ)
    (x u : ℝ → n → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hJ : J*J = -1)
    (hF : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt F (A t*F t) t)
    (hA : ∀ t ∈ Set.Icc (0:ℝ) T, (A t)ᵀ*J+J*A t = 0)
    (hinit : F 0 = 1)
    (hx : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt x (A t *ᵥ x t+u t) t)
    (hint : IntervalIntegrable (fun t => pullback J (F t) *ᵥ u t)
      MeasureTheory.volume 0 T) :
    x T = F T *ᵥ (x 0+∫ t in (0:ℝ)..T, pullback J (F t) *ᵥ u t) := by
  have hd : ∀ t ∈ Set.Icc (0:ℝ) T,
      HasDerivAt (fun s => pullback J (F s) *ᵥ x s)
        (pullback J (F t) *ᵥ u t) t := by
    intro t ht
    have h := mulVec_derivative (pullback_derivative (hF t ht) (hA t ht)) (hx t ht)
    simpa only [neg_mulVec, mulVec_add, mulVec_mulVec, neg_add_cancel_left] using h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [Set.uIcc_of_le hT] using ht)) hint
  have hp0 : pullback J (F 0) = 1 := by
    simp [pullback, hinit, hJ]
    ext i j
    simp
  have hleft : pullback J (F T)*F T = 1 := by
    have hp := SymplecticFlow.preserves_form F A J hF hA hinit T ⟨hT,le_rfl⟩
    change (-J)*(F T)ᵀ*J*F T = 1
    calc
      _ = (-J)*((F T)ᵀ*J*F T) := by noncomm_ring
      _ = 1 := by
        rw [hp, neg_mul, hJ]
        ext i j
        simp
  rw [hp0, one_mulVec] at hi
  have hh : x 0+∫ t in (0:ℝ)..T, pullback J (F t) *ᵥ u t = pullback J (F T) *ᵥ x T := by
    rw [hi]
    abel
  rw [hh, mulVec_mulVec, mul_eq_one_comm.mp hleft, one_mulVec]

end GNC.SymplecticResponse
