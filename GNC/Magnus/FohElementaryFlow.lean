import GNC.Magnus.FohInteractionPolynomial
import GNC.Analysis.DysonIntegral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Exact FOH interaction flow as a convergent sequence of finite
polynomial/sine/cosine expressions. This is an infinite exact representation,
not a claim that the series terminates or is a finite elementary closed form.
-/
noncomputable section
open scoped Matrix.Norms.Operator Topology
open Filter Set
namespace GNC.Magnus
open GNC.Oscillatory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Projection of a finite-dimensional matrix integral. -/
theorem foh_complex_integral_entry {B : ℝ → Matrix ι ι ℂ} {a b : ℝ}
    (hB : IntervalIntegrable B MeasureTheory.volume a b) (i j : ι) :
    (∫ t in a..b, B t) i j = ∫ t in a..b, B t i j := by
  have h := (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.intervalIntegral_comp_comm hB
  simpa using h.symm

/-- Every finite approximant used by the convergence theorem is elementary. -/
theorem foh_dysonApprox_polynomial (B : ℝ → Matrix ι ι ℂ)
    (hB : ∀ i j, Oscillatory.Polynomial (fun t => B t i j)) (n : ℕ) :
    ∀ i j, Oscillatory.Polynomial (fun t => Dyson.approx B n t i j) := by
  have hcB : Continuous B := continuous_pi (fun i => continuous_pi (fun j => (hB i j).continuous))
  induction n with
  | zero => intro i j; exact Oscillatory.Polynomial.constant 0
  | succ n ih =>
    intro i j
    have hc := (Dyson.approx_continuous B hcB n).mul hcB
    have he : (fun t => Dyson.approx B (n+1) t i j) =
        (fun t => (1 : Matrix ι ι ℂ) i j + ∫ s in (0 : ℝ)..t,
          (Dyson.approx B n s * B s) i j) := by
      funext t
      simp only [Dyson.approx, Matrix.add_apply]
      congr 1
      simpa only [Pi.mul_apply] using foh_complex_integral_entry (hc.intervalIntegrable 0 t) i j
    rw [he]
    exact (Oscillatory.Polynomial.constant ((1 : Matrix ι ι ℂ) i j)).add
      ((Oscillatory.Polynomial.sum Finset.univ
        (fun k t => Dyson.approx B n t i k * B t k j)
        (fun k _ => (ih i k).mul (hB k j))).integral 0)

/-- Exactness of the infinite elementary FOH representation follows from the
actual ODE. No slope smallness, Magnus convergence, or special-function premise.
The finite terms remain approximations and have separate factorial bounds. -/
theorem foh_elementary_interaction_convergence (σ : ι → ℝ) (S : Matrix ι ι ℂ)
    (U : ℝ → Matrix ι ι ℂ) (e : ℝ)
    (hU : ∀ t i j, HasDerivAt (fun t => U t i j)
      ((U t * (fohDiagonalGenerator σ + (e : ℂ) • fohCenteredSlope S t)) i j) t)
    (hU0 : U 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    let B := fun t => (e : ℂ) • fohInteractionGenerator σ (fohCenteredSlope S) t
    (Tendsto (fun n => Dyson.approx B n T) atTop (𝓝 (fohRemoveDiagonal σ U T))) ∧
    (∀ n i j, Oscillatory.Polynomial (fun t => Dyson.approx B n t i j)) := by
  dsimp only
  let B := fun t => (e : ℂ) • fohInteractionGenerator σ (fohCenteredSlope S) t
  have hb : ∀ i j, Oscillatory.Polynomial (fun t => B t i j) := by
    intro i j
    exact (foh_interaction_polynomial σ _ (foh_centeredSlope_polynomial S) i j).scale e
  have hcB : Continuous B := continuous_pi (fun i => continuous_pi (fun j => (hb i j).continuous))
  have hv : ∀ t, HasDerivAt (fohRemoveDiagonal σ U)
      (fohRemoveDiagonal σ U t * B t) t := by
    intro t
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [B, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul] using
      foh_removeDiagonal_hasDerivAt σ U (fohCenteredSlope S) e t (hU t) i j
  exact ⟨Dyson.approx_tendsto B _ hcB hv (foh_removeDiagonal_initial σ U hU0) hT,
    foh_dysonApprox_polynomial B hb⟩

theorem foh_mode_norm (σ t : ℝ) : ‖mode σ t‖ = 1 := by
  simp [mode, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Mean rotation does not inflate the induced infinity norm of the
interaction generator: all diagonal rotation factors have unit modulus. -/
theorem foh_interaction_norm (σ : ι → ℝ) (B : ℝ → Matrix ι ι ℂ) (t : ℝ) :
    ‖fohInteractionGenerator σ B t‖ = ‖B t‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  congr 1
  apply Finset.sup_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply NNReal.eq
  simp [fohInteractionGenerator, norm_mul, foh_mode_norm]

/-- Removing or restoring the diagonal rotation preserves this error norm. -/
theorem foh_removeDiagonal_norm (σ : ι → ℝ) (U : ℝ → Matrix ι ι ℂ) (t : ℝ) :
    ‖fohRemoveDiagonal σ U t‖ = ‖U t‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  congr 1
  apply Finset.sup_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply NNReal.eq
  simp [fohRemoveDiagonal, norm_mul, foh_mode_norm]


theorem foh_centeredSlope_norm (S : Matrix ι ι ℂ) (t : ℝ) :
    ‖fohCenteredSlope S t‖ = |t-1/2| * ‖S‖ := by
  have he : fohCenteredSlope S t = ((t : ℂ)-1/2) • S := by
    ext i j
    simp [fohCenteredSlope, Matrix.smul_apply, Complex.real_smul]
  rw [he, norm_smul]
  have he2 : (t : ℂ) - 1/2 = ((t-1/2 : ℝ) : ℂ) := by push_cast; rfl
  rw [he2]
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem foh_removeDiagonal_inverse (σ : ι → ℝ) (U : ℝ → Matrix ι ι ℂ) (t : ℝ) :
    fohRemoveDiagonal (fun i => -σ i) (fohRemoveDiagonal σ U) t = U t := by
  ext i j
  simp only [fohRemoveDiagonal, neg_neg]
  rw [mul_assoc, foh_mode_inverse, mul_one]

theorem foh_restored_error_norm (σ : ι → ℝ) (U P : ℝ → Matrix ι ι ℂ) (t : ℝ) :
    ‖U t - fohRemoveDiagonal (fun i => -σ i) P t‖ =
      ‖fohRemoveDiagonal σ U t - P t‖ := by
  have he : (fun t => U t - fohRemoveDiagonal (fun i => -σ i) P t) =
      fohRemoveDiagonal (fun i => -σ i) (fun t => fohRemoveDiagonal σ U t - P t) := by
    funext t
    ext i j
    simp only [fohRemoveDiagonal, Matrix.sub_apply, sub_mul, neg_neg]
    rw [mul_assoc, foh_mode_inverse, mul_one]
  have hn := foh_removeDiagonal_norm (fun i => -σ i)
    (fun t => fohRemoveDiagonal σ U t - P t) t
  rw [← he] at hn
  exact hn

/-- A full finite-order certificate for the actual centered FOH flow.
The radius K depends on angular slope, not on the magnitude of the removed
mean rotation. The number n counts ordered terms, including the identity.
This bounds real-arithmetic method error, not a floating-point implementation. -/
theorem foh_elementary_slope_certificate [Nonempty ι]
    (σ : ι → ℝ) (S : Matrix ι ι ℂ) (U : ℝ → Matrix ι ι ℂ) (e : ℝ)
    (hU : ∀ t i j, HasDerivAt (fun t => U t i j)
      ((U t * (fohDiagonalGenerator σ + (e : ℂ) • fohCenteredSlope S t)) i j) t)
    (hU0 : U 0 = 1) (n : ℕ) :
    let B := fun t => (e : ℂ) • fohInteractionGenerator σ (fohCenteredSlope S) t
    let K := |e| * ‖S‖ / 2
    ‖U 1 - fohRemoveDiagonal (fun i => -σ i) (Dyson.approx B n) 1‖ ≤
      Real.exp K * K^n / (n.factorial : ℝ) := by
  dsimp only
  let B := fun t => (e : ℂ) • fohInteractionGenerator σ (fohCenteredSlope S) t
  have hb : ∀ i j, Oscillatory.Polynomial (fun t => B t i j) := by
    intro i j
    exact (foh_interaction_polynomial σ _ (foh_centeredSlope_polynomial S) i j).scale e
  have hcB : Continuous B := continuous_pi (fun i => continuous_pi (fun j => (hb i j).continuous))
  have hv : ∀ t, HasDerivAt (fohRemoveDiagonal σ U)
      (fohRemoveDiagonal σ U t * B t) t := by
    intro t
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [B, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul] using
      foh_removeDiagonal_hasDerivAt σ U (fohCenteredSlope S) e t (hU t) i j
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖B t‖ ≤ |e| * ‖S‖ / 2 := by
    intro t ht
    have ha : |t-1/2| ≤ (1/2 : ℝ) := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc
      ‖B t‖ = |e| * (|t-1/2| * ‖S‖) := by
        simp [B, norm_smul, foh_interaction_norm, foh_centeredSlope_norm, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |e| * ((1/2) * ‖S‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) (abs_nonneg _)
      _ = _ := by ring
  rw [foh_restored_error_norm]
  simpa only [mul_one] using Dyson.approx_error_bound_exp B _ hcB hv
    (foh_removeDiagonal_initial σ U hU0) (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 ≤ |e| * ‖S‖ / 2) hbound n

end GNC.Magnus
