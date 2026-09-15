import GNC.Analysis.ExponentialCertificate
import GNC.Analysis.STMComparison
import GNC.Analysis.ArcGronwall

/-! Certify a reported exponential step against an independent continuous
witness. The witness need not interpolate the reported endpoint. Its endpoint
mismatch is explicitly included, along with the exponential evaluation tail
and the continuous ODE defect. These are conditional analytic theorems;
concrete coefficient, norm and evaluation bounds remain certificate inputs.
-/
noncomputable section
open Set MeasureTheory
namespace GNC.ExponentialStep
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [Nontrivial E]
local notation "End" => E →L[ℝ] E

omit [Nontrivial E] in
/-- The independent-witness certificate with a sharper supplied transition
gain. This is the displayed endpoint-mismatch formula in the orbital paper. -/
theorem endpoint_bound_of_gain (Φ : ℝ → Endˣ) (A P D : ℝ → End) (reported : End)
    {a b δ gain mismatch : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ) (hg : 0 ≤ gain)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P (A t*P t+D t) t)
    (hcD : Continuous D) (hinit : P a = (Φ a).val)
    (hD : ∀ t ∈ Icc a b, ‖D t‖ ≤ δ)
    (hgain : (∫ s in a..b, ‖DefectBound.kernel Φ b s‖) ≤ gain)
    (hend : ‖reported-P b‖ ≤ mismatch) :
    ‖reported-(Φ b).val‖ ≤ mismatch+gain*δ := by
  exact (norm_sub_le_norm_sub_add_norm_sub reported (P b) (Φ b).val).trans
    (add_le_add hend (STMComparison.defect_bound Φ A P D hΦ hab hδ hg hcD hP hinit hD hgain))

omit [CompleteSpace E] [Nontrivial E] in
/-- A discrete endpoint may be compared with any validated continuous
witness. No differentiability of the numerical solver is assumed. -/
theorem endpoint_bound (A P Q D : ℝ → End) (reported : End)
    {a b L δ mismatch : ℝ} (hab : a ≤ b)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P (A t*P t+D t) t)
    (hQ : ∀ t ∈ Icc a b, HasDerivAt Q (A t*Q t) t)
    (hinit : P a = Q a)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ L)
    (hD : ∀ t ∈ Icc a b, ‖D t‖ ≤ δ)
    (hend : ‖reported-P b‖ ≤ mismatch) :
    ‖reported-Q b‖ ≤ mismatch+gronwallBound 0 L δ (b-a) := by
  exact (norm_sub_le_norm_sub_add_norm_sub reported (P b) (Q b)).trans
    (add_le_add hend (STMComparison.defect_bound_of_generator_norm
      A P Q D hP hQ hinit hA hD b ⟨hab,le_rfl⟩))

/-- Certify an exponential-based method by an independent ODE witness.
`matching` bounds a finite polynomial difference, not an analytic tail.
`rounding` must bound the actual reported matrix against the actual matrix
exponential, for example using `ExponentialCertificate.evaluation_bound`.
The witness may be a polynomial of any degree. -/
theorem exponential_step_bound (A P Q D : ℝ → End) (x reported : End)
    {a b L δ r rounding matching : ℝ} (hab : a ≤ b)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P (A t*P t+D t) t)
    (hQ : ∀ t ∈ Icc a b, HasDerivAt Q (A t*Q t) t)
    (hinit : P a = Q a)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ L)
    (hD : ∀ t ∈ Icc a b, ‖D t‖ ≤ δ)
    (hx : ‖x‖ ≤ r) (hr : r ≤ 1) (n : ℕ) (hn : 0 < n)
    (hreported : ‖reported-NormedSpace.exp x‖ ≤ rounding)
    (hmatch : ‖ExponentialCertificate.polynomial x n-P b‖ ≤ matching) :
    ‖reported-Q b‖ ≤
      rounding+r^n*(n+1)/(Nat.factorial n*n)+matching+
        gronwallBound 0 L δ (b-a) := by
  apply endpoint_bound A P Q D reported hab hP hQ hinit hA hD
  calc
    ‖reported-P b‖ ≤ ‖reported-NormedSpace.exp x‖+‖NormedSpace.exp x-P b‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ rounding+(r^n*(n+1)/(Nat.factorial n*n)+matching) :=
      add_le_add hreported
        ((norm_sub_le_norm_sub_add_norm_sub _ (ExponentialCertificate.polynomial x n) _).trans
          (add_le_add (ExponentialCertificate.remainder_bound x hx hr n hn) hmatch))
    _ = _ := by ring

omit [CompleteSpace E] [Nontrivial E] in
/-- A certificate using only a finite endpoint check and continuous ODE
defect. An exponential evaluator need not be trusted: its stored output is
checked directly against the independent witness at the endpoint. -/
theorem endpoint_bound_finite (A P Q D : ℝ → End) (reported : End)
    {a b L δ mismatch : ℝ} (hab : a ≤ b) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P (A t*P t+D t) t)
    (hQ : ∀ t ∈ Icc a b, HasDerivAt Q (A t*Q t) t)
    (hinit : P a = Q a)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ L)
    (hD : ∀ t ∈ Icc a b, ‖D t‖ ≤ δ)
    (hend : ‖reported-P b‖ ≤ mismatch)
    (hsmall : L*(b-a) ≤ 1) (n : ℕ) (hn : 0 < n) :
    ‖reported-Q b‖ ≤ mismatch+δ*(b-a)*
      (ExponentialCertificate.scalarPolynomial (L*(b-a)) n+
        (L*(b-a))^n*(n+1)/(Nat.factorial n*n)) := by
  apply (endpoint_bound A P Q D reported hab hP hQ hinit hA hD hend).trans
  apply add_le_add le_rfl
  have hh : 0 ≤ b-a := sub_nonneg.mpr hab
  have hg := ArcGronwall.gronwall_upper (δ := 0) hL hδ hh
  simp only [zero_add] at hg
  exact hg.trans (mul_le_mul_of_nonneg_left
    (ExponentialCertificate.scalar_bound (mul_nonneg hL hh) hsmall n hn)
    (mul_nonneg hδ hh))

end GNC.ExponentialStep
