import GNC.Magnus.GaussRemainder
import Mathlib.Analysis.Calculus.Taylor

/-! A nonpolynomial generator's cubic remainder is charged both to the ODE
witness defect and to the two Gauss samples. The remainder is a uniform
analytic bound over the step, not a sampled diagnostic.
-/
noncomputable section
namespace GNC.Magnus.GaussRemainder
open Polynomial AlgebraPolynomial Set
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V] [Nontrivial V]
local notation "End" => V →L[ℝ] V

def generatorSize (a b c d : End) (h R : ℝ) : ℝ :=
  majorant (generator a b c d) 1+R*h^4

def witnessBudget (a b c d : End) (h R : ℝ) : ℝ :=
  h^5*(majorant ((gaussLeftExponent a b c d (Real.sqrt 3/6))^5) 1/100+
    majorant (mismatch a b c d) 1+
    (majorant (residual a b c d) 1+R*majorant (witness a b c d) 1)*
      Real.exp (generatorSize a b c d h R*h))

def nodeBudget (a b c d : End) (h R : ℝ) : ℝ :=
  h^5*R*(1+Real.sqrt 3*h/6*(2*majorant (generator a b c d) 1+R*h^4))

def exponentRadius (a b c d : End) (h R : ℝ) : ℝ :=
  h*majorant (gaussLeftExponent a b c d (Real.sqrt 3/6)) 1+nodeBudget a b c d h R

def localBudget (a b c d : End) (h R : ℝ) : ℝ :=
  witnessBudget a b c d h R+Real.exp (exponentRadius a b c d h R)*nodeBudget a b c d h R

theorem gauss_fractions_mem :
    (1/2-Real.sqrt 3/6 : ℝ) ∈ Icc 0 1 ∧ (1/2+Real.sqrt 3/6 : ℝ) ∈ Icc 0 1 := by
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  constructor <;> constructor <;> dsimp <;> nlinarith

theorem gauss_times_mem {h : ℝ} (h0 : 0 ≤ h) :
    ((1/2-Real.sqrt 3/6)*h : ℝ) ∈ Icc 0 h ∧
    ((1/2+Real.sqrt 3/6)*h : ℝ) ∈ Icc 0 h := by
  constructor
  · exact ⟨mul_nonneg gauss_fractions_mem.1.1 h0,
      (mul_le_mul_of_nonneg_right gauss_fractions_mem.1.2 h0).trans_eq (one_mul h)⟩
  · exact ⟨mul_nonneg gauss_fractions_mem.2.1 h0,
      (mul_le_mul_of_nonneg_right gauss_fractions_mem.2.2 h0).trans_eq (one_mul h)⟩

omit [CompleteSpace V] [Nontrivial V] in
theorem generator_norm_of_remainder (a b c d : End) (B : ℝ → End)
    {h R : ℝ} (h1 : h ≤ 1) (hR : 0 ≤ R)
    (hrem : ∀ t ∈ Icc 0 h, ‖B t-value (generator a b c d) t‖ ≤ R*t^4)
    {t : ℝ} (ht : t ∈ Icc 0 h) : ‖B t‖ ≤ generatorSize a b c d h R := by
  have hp := norm_value_le (generator a b c d)
    (show |t| ≤ 1 by rw [abs_of_nonneg ht.1]; exact ht.2.trans h1)
  have hr := (hrem t ht).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ ht.1 ht.2 4) hR)
  have hn := norm_sub_le (B t-value (generator a b c d) t) (-value (generator a b c d) t)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hn
  exact hn.trans (by dsimp [generatorSize]; linarith)

/-- The cubic Gauss step compared with the true, nonpolynomial ODE. The
missing generator terms remain in the witness defect as `(Γ-B)P`. -/
theorem witness_error_with_remainder (a b c d : End) (B Q : ℝ → End)
    {h R : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (hR : 0 ≤ R)
    (hsmall : h*majorant (gaussLeftExponent a b c d (Real.sqrt 3/6)) 1 ≤ 1)
    (hrem : ∀ t ∈ Icc 0 h, ‖B t-value (generator a b c d) t‖ ≤ R*t^4)
    (hQ : ∀ t ∈ Icc 0 h, HasDerivAt Q (B t*Q t) t) (hinit : Q 0 = 1) :
    ‖NormedSpace.exp (value (gaussLeftExponent a b c d (Real.sqrt 3/6)) h)-Q h‖ ≤
      witnessBudget a b c d h R := by
  let P := value (witness a b c d)
  let D := fun t => (value (generator a b c d) t-B t)*P t+value (residual a b c d) t
  let L := generatorSize a b c d h R
  let C := majorant (residual a b c d) 1+R*majorant (witness a b c d) 1
  have hL : 0 ≤ L := add_nonneg (majorant_nonnegative _ (by norm_num)) (by positivity)
  have hC : 0 ≤ C := add_nonneg (majorant_nonnegative _ (by norm_num))
    (mul_nonneg hR (majorant_nonnegative _ (by norm_num)))
  have hP (t : ℝ) : HasDerivAt P (B t*P t+D t) t := by
    convert witness_derivative a b c d t using 1
    dsimp [P,D]; noncomm_ring
  have hD (t : ℝ) (ht : t ∈ Icc 0 h) : ‖D t‖ ≤ h^4*C := by
    have hp := norm_value_le (witness a b c d)
      (show |t| ≤ 1 by rw [abs_of_nonneg ht.1]; exact ht.2.trans h1)
    have hr := vanishing_bound (residual a b c d) 4 (residual_vanishes a b c d)
      ht.1 (ht.2.trans h1)
    have hb : ‖value (generator a b c d) t-B t‖ ≤ R*t^4 := by
      rw [norm_sub_rev]; exact hrem t ht
    calc
      ‖D t‖ ≤ ‖value (generator a b c d) t-B t‖*‖P t‖+‖value (residual a b c d) t‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
      _ ≤ R*t^4*majorant (witness a b c d) 1+t^4*majorant (residual a b c d) 1 :=
        add_le_add (mul_le_mul hb hp (norm_nonneg _) (by positivity)) hr
      _ = t^4*C := by dsimp [C]; ring
      _ ≤ h^4*C := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.1 ht.2 4) hC
  have hw := STMComparison.defect_bound_of_generator_norm B P Q D
    (fun t _ => hP t) hQ ((witness_initial a b c d).trans hinit.symm)
    (fun _ ht => generator_norm_of_remainder a b c d B h1 hR hrem ht) hD h ⟨h0,le_rfl⟩
  simp only [sub_zero] at hw
  have hg := ArcGronwall.gronwall_upper (δ := 0) hL (mul_nonneg (pow_nonneg h0 4) hC) h0
  simp only [zero_add] at hg
  have he := exponential_witness_error a b c d h0 h1 hsmall
  calc
    _ ≤ ‖NormedSpace.exp (value (gaussLeftExponent a b c d (Real.sqrt 3/6)) h)-P h‖+
        ‖P h-Q h‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ h^5*(majorant ((gaussLeftExponent a b c d (Real.sqrt 3/6))^5) 1/100+
        majorant (mismatch a b c d) 1)+(h^4*C*h)*Real.exp (L*h) := add_le_add he (hw.trans hg)
    _ = _ := by dsimp [witnessBudget,C,L]; ring

omit [CompleteSpace V] [Nontrivial V] in
/-- The cubic approximation error also enters the Gauss samples. This term
cannot be accounted for solely by changing the ODE witness's defect. -/
theorem gauss_exponent_error_of_remainder (a b c d : End) (B : ℝ → End)
    {h R : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (hR : 0 ≤ R)
    (hrem : ∀ t ∈ Icc 0 h, ‖B t-value (generator a b c d) t‖ ≤ R*t^4) :
    ‖gaussStepExponent (B ((1/2-Real.sqrt 3/6)*h)) (B ((1/2+Real.sqrt 3/6)*h)) h-
      value (gaussLeftExponent a b c d (Real.sqrt 3/6)) h‖ ≤ nodeBudget a b c d h R := by
  have he (t : ℝ) (ht : t ∈ Icc 0 h) : ‖B t-value (generator a b c d) t‖ ≤ R*h^4 :=
    (hrem t ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 4) hR)
  have htimes := gauss_times_mem h0
  have hm : ‖value (generator a b c d) ((1/2-Real.sqrt 3/6)*h)‖ ≤
      majorant (generator a b c d) 1 := norm_value_le _
    (by rw [abs_of_nonneg htimes.1.1]; exact htimes.1.2.trans h1)
  rw [exponent_value]
  apply (gauss_exponent_perturbation _ _ _ _ h0
    (he _ htimes.1) (he _ htimes.2) hm
    (generator_norm_of_remainder a b c d B h1 hR hrem htimes.2)).trans_eq
  dsimp [nodeBudget, generatorSize]
  ring

/-- A quantitative local truncation certificate for a nonpolynomial
generator with a validated cubic remainder. The reported exponent here
uses the actual generator at the actual Gauss nodes. Floating-point node,
exponential and multiplication errors are separate, already proved budgets. -/
theorem local_error_with_remainder (a b c d : End) (B Q : ℝ → End)
    {h R : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (hR : 0 ≤ R)
    (hsmall : h*majorant (gaussLeftExponent a b c d (Real.sqrt 3/6)) 1 ≤ 1)
    (hrem : ∀ t ∈ Icc 0 h, ‖B t-value (generator a b c d) t‖ ≤ R*t^4)
    (hQ : ∀ t ∈ Icc 0 h, HasDerivAt Q (B t*Q t) t) (hinit : Q 0 = 1) :
    ‖NormedSpace.exp (gaussStepExponent
        (B ((1/2-Real.sqrt 3/6)*h)) (B ((1/2+Real.sqrt 3/6)*h)) h)-Q h‖ ≤
      localBudget a b c d h R := by
  let X := gaussStepExponent (B ((1/2-Real.sqrt 3/6)*h)) (B ((1/2+Real.sqrt 3/6)*h)) h
  let Y := value (gaussLeftExponent a b c d (Real.sqrt 3/6)) h
  have herr : ‖X-Y‖ ≤ nodeBudget a b c d h R :=
    gauss_exponent_error_of_remainder a b c d B h0 h1 hR hrem
  have hY := exponent_norm a b c d h0 h1
  have hn : 0 ≤ nodeBudget a b c d h R := (norm_nonneg _).trans herr
  have hYr : ‖Y‖ ≤ exponentRadius a b c d h R := by dsimp [exponentRadius]; linarith
  have hXr : ‖X‖ ≤ exponentRadius a b c d h R := by
    have ht := norm_sub_le (X-Y) (-Y)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
    dsimp [exponentRadius]; linarith
  have he := (ExponentialCertificate.perturbation_bound X Y hXr hYr).trans
    (mul_le_mul_of_nonneg_left herr (Real.exp_pos _).le)
  have hw := witness_error_with_remainder a b c d B Q h0 h1 hR hsmall hrem hQ hinit
  exact (norm_sub_le_norm_sub_add_norm_sub (NormedSpace.exp X) (NormedSpace.exp Y) (Q h)).trans
    ((add_le_add he hw).trans_eq (by dsimp [localBudget]; ring))

omit [CompleteSpace V] [Nontrivial V] in
/-- Explicitly factor the fifth power of the step duration. The remaining
coefficient depends on the reference coefficients and cubic remainder. -/
theorem localBudget_fifth_order (a b c d : End) (h R : ℝ) :
    localBudget a b c d h R = h^5*
      (majorant ((gaussLeftExponent a b c d (Real.sqrt 3/6))^5) 1/100+
       majorant (mismatch a b c d) 1+
       (majorant (residual a b c d) 1+R*majorant (witness a b c d) 1)*
         Real.exp (generatorSize a b c d h R*h)+
       Real.exp (exponentRadius a b c d h R)*R*
         (1+Real.sqrt 3*h/6*(2*majorant (generator a b c d) 1+R*h^4))) := by
  dsimp [localBudget, witnessBudget, nodeBudget]
  ring

omit [CompleteSpace V] [Nontrivial V] in
/-- Released mathlib's vector-valued Taylor theorem supplies one sufficient
cubic-remainder bound. Its constant here is M/3!, not the sharper M/4!;
that distinction is retained rather than silently changing the theorem. -/
theorem cubic_remainder_of_four_derivatives (B : ℝ → End) {h M t : ℝ}
    (h0 : 0 ≤ h) (hB : ContDiffOn ℝ 4 B (Icc 0 h)) (ht : t ∈ Icc 0 h)
    (hM : ∀ s ∈ Icc 0 h, ‖iteratedDerivWithin 4 B (Icc 0 h) s‖ ≤ M) :
    ‖B t-value (generator (B 0) (iteratedDerivWithin 1 B (Icc 0 h) 0)
      ((1/2:ℝ) • iteratedDerivWithin 2 B (Icc 0 h) 0)
      ((1/6:ℝ) • iteratedDerivWithin 3 B (Icc 0 h) 0)) t‖ ≤ (M/6)*t^4 := by
  have he : taylorWithinEval B 3 (Icc 0 h) 0 t =
      value (generator (B 0) (iteratedDerivWithin 1 B (Icc 0 h) 0)
        ((1/2:ℝ) • iteratedDerivWithin 2 B (Icc 0 h) 0)
        ((1/6:ℝ) • iteratedDerivWithin 3 B (Icc 0 h) 0)) t := by
    norm_num [taylorWithinEval_succ, generator, value_add, value_monomial, smul_smul]
    simp only [value_smul, value_monomial, value_C, smul_smul]
  have hb := taylor_mean_remainder_bound (n := 3) h0 hB ht hM
  rw [he] at hb
  convert hb using 1; norm_num [Nat.factorial]; ring

/-- End-to-end analytic local bound under a fourth-derivative enclosure.
The coefficient equalities specify the actual Taylor jet, and `M/6` is
the conservative remainder constant provided by the reused mathlib theorem.
No Magnus truncation error is assumed among the hypotheses. -/
theorem local_error_of_four_derivatives (a b c d : End) (B Q : ℝ → End)
    {h M : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (hM0 : 0 ≤ M)
    (hB : ContDiffOn ℝ 4 B (Icc 0 h))
    (hM : ∀ t ∈ Icc 0 h, ‖iteratedDerivWithin 4 B (Icc 0 h) t‖ ≤ M)
    (hcoeff : a = B 0 ∧ b = iteratedDerivWithin 1 B (Icc 0 h) 0 ∧
      c = (1/2:ℝ) • iteratedDerivWithin 2 B (Icc 0 h) 0 ∧
      d = (1/6:ℝ) • iteratedDerivWithin 3 B (Icc 0 h) 0)
    (hsmall : h*majorant (gaussLeftExponent a b c d (Real.sqrt 3/6)) 1 ≤ 1)
    (hQ : ∀ t ∈ Icc 0 h, HasDerivAt Q (B t*Q t) t) (hinit : Q 0 = 1) :
    ‖NormedSpace.exp (gaussStepExponent
        (B ((1/2-Real.sqrt 3/6)*h)) (B ((1/2+Real.sqrt 3/6)*h)) h)-Q h‖ ≤
      localBudget a b c d h (M/6) := by
  rcases hcoeff with ⟨rfl,rfl,rfl,rfl⟩
  exact local_error_with_remainder _ _ _ _ B Q h0 h1 (by positivity) hsmall
    (fun _ ht => cubic_remainder_of_four_derivatives B h0 hB ht hM) hQ hinit

omit [CompleteSpace V] [Nontrivial V] in
/-- A step-independent (usually coarser) constant makes the fifth-order
statement explicit on 0 ≤ h ≤ 1. Certification should use `localBudget`
at the actual step when it is tighter. -/
theorem localBudget_uniform (a b c d : End) {h R : ℝ}
    (h0 : 0 ≤ h) (h1 : h ≤ 1) (hR : 0 ≤ R) :
    localBudget a b c d h R ≤ h^5*localBudget a b c d 1 R := by
  have hg := majorant_nonnegative (generator a b c d) (by norm_num : (0:ℝ) ≤ 1)
  have hp := majorant_nonnegative (gaussLeftExponent a b c d (Real.sqrt 3/6)) (by norm_num : (0:ℝ) ≤ 1)
  have hw := majorant_nonnegative (witness a b c d) (by norm_num : (0:ℝ) ≤ 1)
  have hd := majorant_nonnegative (residual a b c d) (by norm_num : (0:ℝ) ≤ 1)
  have hm := majorant_nonnegative (mismatch a b c d) (by norm_num : (0:ℝ) ≤ 1)
  have hp5 := majorant_nonnegative ((gaussLeftExponent a b c d (Real.sqrt 3/6))^5)
    (by norm_num : (0:ℝ) ≤ 1)
  rw [localBudget_fifth_order, localBudget_fifth_order]
  simp only [one_pow, one_mul, mul_one]
  dsimp [generatorSize, exponentRadius, nodeBudget]
  simp only [one_pow, one_mul, mul_one]
  generalize hgen : majorant (generator a b c d) 1 = cg at *
  generalize hexp : majorant (gaussLeftExponent a b c d (Real.sqrt 3/6)) 1 = co at *
  generalize hwit : majorant (witness a b c d) 1 = cw at *
  generalize hdef : majorant (residual a b c d) 1 = cd at *
  generalize hmis : majorant (mismatch a b c d) 1 = cm at *
  generalize hpower : majorant ((gaussLeftExponent a b c d (Real.sqrt 3/6))^5) 1 = c5 at *
  have h4 : h^4 ≤ 1 := pow_le_one₀ h0 h1
  have h5 : h^5 ≤ 1 := pow_le_one₀ h0 h1
  have hr4 : R*h^4 ≤ R := (mul_le_mul_of_nonneg_left h4 hR).trans_eq (mul_one _)
  have hr5 : h^5*R ≤ R := (mul_le_mul_of_nonneg_right h5 hR).trans_eq (one_mul _)
  have ho : h*co ≤ co := (mul_le_mul_of_nonneg_right h1 hp).trans_eq (one_mul _)
  have hs : Real.sqrt 3*h ≤ Real.sqrt 3 :=
    (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)).trans_eq (mul_one _)
  have hl : (cg+R*h^4)*h ≤ cg+R :=
    (mul_le_mul (add_le_add le_rfl hr4) h1 h0 (add_nonneg hg hR)).trans_eq (mul_one _)
  gcongr

end GNC.Magnus.GaussRemainder
