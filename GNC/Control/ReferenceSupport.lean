import GNC.Control.ThrustIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Directional certificates retaining a known time-varying error generator.

The adjoint cancels the entire retained A(t), without freezing it or bounding
its variation by independent matrices. A single common pointing parameter is
then bounded after accumulating its response. The nonlinear residual remains
an explicit directional integral. These are classical adjoint identities used
with a geometric error model, not an exclusive property of Lie coordinates.
-/
noncomputable section
open Matrix MeasureTheory Set
namespace GNC.ReferenceSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rows (ell : E →L[ℝ] ℝ) (B : Vec3 →L[ℝ] E) : Vec3 :=
  ![ell (B ![1,0,0]), ell (B ![0,1,0]), ell (B ![0,0,1])]

theorem input_pairing (ell : E →L[ℝ] ℝ) (B : Vec3 →L[ℝ] E) (q : Vec3) :
    rows ell B ⬝ᵥ q = ell (B q) := by
  have he : q = q 0 • ![1,0,0]+q 1 • ![0,1,0]+q 2 • ![0,0,1] := by
    ext i
    fin_cases i <;> simp
  conv_rhs =>
    rw [he]
    simp only [map_add, map_smul, smul_eq_mul]
  simp [rows, dotProduct, Fin.sum_univ_succ, mul_comm, add_assoc]

theorem rows_continuous (ell : ℝ → E →L[ℝ] ℝ) (B : ℝ → Vec3 →L[ℝ] E)
    (hell : Continuous ell) (hB : Continuous B) : Continuous (fun t => rows (ell t) (B t)) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [rows]
  all_goals exact hell.clm_apply (hB.clm_apply continuous_const)

/-- The complete known A(t) cancels, including its moving gravity gradient
and frame terms. No commutativity or small rate of variation is required. -/
theorem adjoint_derivative (A : ℝ → E →L[ℝ] E)
    (ell : ℝ → E →L[ℝ] ℝ) (x u : ℝ → E) {t : ℝ}
    (hell : HasDerivAt ell (-(ell t).comp (A t)) t)
    (hx : HasDerivAt x (A t (x t)+u t) t) :
    HasDerivAt (fun s => ell s (x s)) (ell t (u t)) t := by
  convert hell.clm_apply hx using 1
  simp

/-- Actual error dynamics with a common constant parameter q and a residual.
To apply this to nonlinear dynamics, r is its actual residual along x; a
regional proof must justify any subsequent bound on that residual. -/
theorem endpoint_identity (A : ℝ → E →L[ℝ] E)
    (B : ℝ → Vec3 →L[ℝ] E) (ell : ℝ → E →L[ℝ] ℝ) (x r : ℝ → E)
    (q : Vec3) {T : ℝ} (hT : 0 ≤ T)
    (hellc : Continuous ell) (hBc : Continuous B) (hrc : Continuous r)
    (hell : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt ell (-(ell t).comp (A t)) t)
    (hx : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt x (A t (x t)+B t q+r t) t) :
    ell T (x T) = ell 0 (x 0)+(∫ t in (0:ℝ)..T, rows (ell t) (B t)) ⬝ᵥ q+
      ∫ t in (0:ℝ)..T, ell t (r t) := by
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) :
      HasDerivAt (fun s => ell s (x s))
        (rows (ell t) (B t) ⬝ᵥ q+ell t (r t)) t := by
    rw [input_pairing, ← map_add]
    exact adjoint_derivative A ell x (fun s => B s q+r s) (hell t ht)
      (by simpa only [add_assoc] using hx t ht)
  have hh := rows_continuous ell B hellc hBc
  have hi : IntervalIntegrable (fun t => rows (ell t) (B t) ⬝ᵥ q) volume 0 T :=
    (hh.dotProduct continuous_const).intervalIntegrable 0 T
  have hj : IntervalIntegrable (fun t => ell t (r t)) volume 0 T :=
    (hellc.clm_apply hrc).intervalIntegrable 0 T
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le hT] using ht)) (hi.add hj)
  rw [intervalIntegral.integral_add hi hj,
    ThrustSupport.integral_pairing _ q (hh.intervalIntegrable 0 T)] at he
  linarith

/-- Apply the actual ODE identity separately on burn/coast arcs. The paired
boundary values F telescope, while the SAME parameter q is accumulated before
it is bounded. No derivative or continuity across an input switch is assumed. -/
theorem endpoint_from_arcs (N : ℕ) (T F : ℕ → ℝ)
    (A : ℕ → ℝ → E →L[ℝ] E) (B : ℕ → ℝ → Vec3 →L[ℝ] E)
    (ell : ℕ → ℝ → E →L[ℝ] ℝ) (x r : ℕ → ℝ → E) (q : Vec3)
    (hT : ∀ j < N, 0 ≤ T j)
    (hellc : ∀ j < N, Continuous (ell j)) (hBc : ∀ j < N, Continuous (B j))
    (hrc : ∀ j < N, Continuous (r j))
    (hell : ∀ j < N, ∀ t ∈ Icc (0:ℝ) (T j),
      HasDerivAt (ell j) (-(ell j t).comp (A j t)) t)
    (hx : ∀ j < N, ∀ t ∈ Icc (0:ℝ) (T j),
      HasDerivAt (x j) (A j t (x j t)+B j t q+r j t) t)
    (hstart : ∀ j < N, ell j 0 (x j 0) = F j)
    (hend : ∀ j < N, ell j (T j) (x j (T j)) = F (j+1)) :
    F N = F 0+
      (∑ j ∈ Finset.range N, ∫ t in (0:ℝ)..T j, rows (ell j t) (B j t)) ⬝ᵥ q+
      ∑ j ∈ Finset.range N, ∫ t in (0:ℝ)..T j, ell j t (r j t) := by
  have he (j : ℕ) (hj : j ∈ Finset.range N) :
      F (j+1)-F j = (∫ t in (0:ℝ)..T j, rows (ell j t) (B j t)) ⬝ᵥ q+
        ∫ t in (0:ℝ)..T j, ell j t (r j t) := by
    have hn := Finset.mem_range.mp hj
    have h := endpoint_identity (A j) (B j) (ell j) (x j) (r j) q
      (hT j hn) (hellc j hn) (hBc j hn) (hrc j hn) (hell j hn) (hx j hn)
    rw [hstart j hn, hend j hn] at h
    linarith
  have hs := Finset.sum_congr rfl he
  rw [Finset.sum_range_sub, Finset.sum_add_distrib] at hs
  have hp : (∑ j ∈ Finset.range N, ∫ t in (0:ℝ)..T j, rows (ell j t) (B j t)) ⬝ᵥ q =
      ∑ j ∈ Finset.range N, (∫ t in (0:ℝ)..T j, rows (ell j t) (B j t)) ⬝ᵥ q := by
    exact map_sum (ThrustSupport.dotMap q) _ _
  rw [hp]
  linarith

/-- Bound a coherent pointing error after accumulating the known response.
The remainder envelope d is integrated separately; it is not discarded or
included in a floating-point solver tolerance. -/
theorem endpoint_ball_bound (A : ℝ → E →L[ℝ] E)
    (B : ℝ → Vec3 →L[ℝ] E) (ell : ℝ → E →L[ℝ] ℝ) (x r : ℝ → E)
    (q n : Vec3) (d : ℝ → ℝ) {T δ : ℝ} (hT : 0 ≤ T)
    (hellc : Continuous ell) (hBc : Continuous B) (hrc : Continuous r) (hdc : Continuous d)
    (hell : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt ell (-(ell t).comp (A t)) t)
    (hx : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt x (A t (x t)+B t q+r t) t)
    (hq : enorm (q-n) ≤ δ)
    (hr : ∀ t ∈ Icc (0:ℝ) T, |ell t (r t)| ≤ d t) :
    ell T (x T) ≤ ell 0 (x 0)+
      ThrustSupport.ballBound n (∫ t in (0:ℝ)..T, rows (ell t) (B t)) δ+
      ∫ t in (0:ℝ)..T, d t := by
  rw [endpoint_identity A B ell x r q hT hellc hBc hrc hell hx]
  apply add_le_add
  · exact add_le_add le_rfl (ThrustSupport.chord_ball_support n _ q δ hq)
  · apply intervalIntegral.integral_mono_on hT
      ((hellc.clm_apply hrc).intervalIntegrable 0 T) (hdc.intervalIntegrable 0 T)
    intro t ht
    exact (le_abs_self _).trans (hr t ht)

/-- The reduction in a directional uncertainty budget from preserving the
same parameter through the whole burn. It need not be positive. -/
def coherenceGain (h : ℝ → Vec3) (T δ : ℝ) : ℝ :=
  δ*((∫ t in (0:ℝ)..T, enorm (h t))-enorm (∫ t in (0:ℝ)..T, h t))

theorem coherenceGain_nonneg (h : ℝ → Vec3) {T δ : ℝ} (hT : 0 ≤ T)
    (hh : IntervalIntegrable h volume 0 T) (hδ : 0 ≤ δ) : 0 ≤ coherenceGain h T δ :=
  mul_nonneg hδ (sub_nonneg.mpr (ThrustSupport.enorm_integral_le h hT hh))

/-- Exact comparison with the pointwise ball budget, keeping the same
initial-error and nonlinear-remainder budgets in either calculation. -/
theorem budget_difference (h : ℝ → Vec3) (n : Vec3) (T δ : ℝ)
    (hh : IntervalIntegrable h volume 0 T) :
    (∫ t in (0:ℝ)..T, h t ⬝ᵥ n)+δ*(∫ t in (0:ℝ)..T, enorm (h t))-
      ThrustSupport.ballBound n (∫ t in (0:ℝ)..T, h t) δ = coherenceGain h T δ := by
  rw [ThrustSupport.integral_pairing h n hh]
  simp only [ThrustSupport.ballBound, coherenceGain]
  ring

end GNC.ReferenceSupport
