import GNC.Applications.Rendezvous.HCWMatrix
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Compactness.Lindelof

/-! Isolated and measure-zero singular transfer horizons. The analytic
identity principle is reused from mathlib; continuity alone is not used
as a substitute for analyticity. -/
noncomputable section
open Matrix Real Set Filter MeasureTheory
open scoped Topology
namespace GNC.SingularTimes

/-- A nontrivial analytic scalar function has a closed discrete zero set. -/
theorem analytic_zeros_closed_discrete (f : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f univ) (h : ∃ x, f x ≠ 0) :
    IsClosed {t | f t = 0} ∧ IsDiscrete {t | f t = 0} := by
  have hn := hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ
  have he : ∀ᶠ t in codiscrete ℝ, f t ≠ 0 := hn.resolve_left (by
    intro hz
    obtain ⟨x,hx⟩ := h
    exact hx (hz (mem_univ x)))
  have hd := mem_codiscrete'.mp he
  simpa only [Set.compl_setOf, not_not, ← isClosed_compl_iff] using hd

theorem analytic_zeros_countable (f : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f univ) (h : ∃ x, f x ≠ 0) :
    {t | f t = 0}.Countable :=
  (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (analytic_zeros_closed_discrete f hf h).2

theorem analytic_zeros_measure_zero (f : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f univ) (h : ∃ x, f x ≠ 0) :
    volume {t | f t = 0} = 0 :=
  (analytic_zeros_countable f hf h).measure_zero volume

theorem analytic_zeros_finite_interval (f : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f univ) (h : ∃ x, f x ≠ 0) (a b : ℝ) :
    (Icc a b ∩ {t | f t = 0}).Finite := by
  obtain ⟨hc,hd⟩ := analytic_zeros_closed_discrete f hf h
  exact (isCompact_Icc.inter_right hc).finite (hd.mono inter_subset_right)

theorem hcw_det (n t : ℝ) :
    (HCWMatrix.rv n t).det = (1/n)^3 * (sin (n*t)*inPlaneDet (n*t)) := by
  rw [HCWMatrix.rv_scaled, Matrix.det_smul, det_pv]
  rfl

theorem hcw_det_analytic (n : ℝ) :
    AnalyticOnNhd ℝ (fun t => (HCWMatrix.rv n t).det) univ := by
  intro t _
  simp only [hcw_det, inPlaneDet]
  have hi : AnalyticAt ℝ (fun t : ℝ => n*t) t := analyticAt_const.mul analyticAt_id
  exact analyticAt_const.mul ((Real.analyticAt_sin.comp hi).mul
    ((analyticAt_const.sub (analyticAt_const.mul (Real.analyticAt_cos.comp hi))).sub
      ((analyticAt_const.mul hi).mul (Real.analyticAt_sin.comp hi))))

theorem hcw_det_nontrivial (n : ℝ) (hn : n ≠ 0) :
    ∃ t, (HCWMatrix.rv n t).det ≠ 0 := by
  refine ⟨(π/2)/n, ?_⟩
  rw [hcw_det, mul_div_cancel₀ _ hn]
  simp only [inPlaneDet, sin_pi_div_two, cos_pi_div_two, mul_zero, sub_zero, mul_one, one_mul]
  exact mul_ne_zero (pow_ne_zero _ (one_div_ne_zero hn)) (by linarith [pi_lt_four])

/-- The corrected circular singular set includes all determinant roots,
including the extra roots established in `SingularTimes`. -/
theorem hcw_singular_closed_discrete (n : ℝ) (hn : n ≠ 0) :
    IsClosed {t | (HCWMatrix.rv n t).det = 0} ∧
      IsDiscrete {t | (HCWMatrix.rv n t).det = 0} :=
  analytic_zeros_closed_discrete _ (hcw_det_analytic n) (hcw_det_nontrivial n hn)

theorem hcw_singular_measure_zero (n : ℝ) (hn : n ≠ 0) :
    volume {t | (HCWMatrix.rv n t).det = 0} = 0 :=
  analytic_zeros_measure_zero _ (hcw_det_analytic n) (hcw_det_nontrivial n hn)

theorem hcw_singular_finite_interval (n : ℝ) (hn : n ≠ 0) (a b : ℝ) :
    (Icc a b ∩ {t | (HCWMatrix.rv n t).det = 0}).Finite :=
  analytic_zeros_finite_interval _ (hcw_det_analytic n) (hcw_det_nontrivial n hn) a b

end GNC.SingularTimes
