import GNC.Analysis.DysonIntegral

/-! A compact identity for the first two ordered insertions of a right flow.
The commutator term has the sign fixed by `Y' = Y B`. This is an exact
identity between finite approximants, not a finite exact-flow claim. -/
noncomputable section
open Set
namespace GNC.OrderedQuadratic
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

def first (B : ℝ → E) (t : ℝ) : E := ∫ s in (0 : ℝ)..t, B s

def coning (B : ℝ → E) (t : ℝ) : E :=
  (1/2 : ℝ) • ∫ s in (0 : ℝ)..t, first B s * B s - B s * first B s

def predictor (B : ℝ → E) (t : ℝ) : E :=
  1 + first B t + (1/2 : ℝ) • (first B t * first B t) + coning B t

theorem first_hasDerivAt (B : ℝ → E) (hB : Continuous B) (t : ℝ) :
    HasDerivAt (first B) (B t) t :=
  intervalIntegral.integral_hasDerivAt_right (hB.intervalIntegrable 0 t)
    hB.aestronglyMeasurable.stronglyMeasurableAtFilter hB.continuousAt

theorem first_continuous (B : ℝ → E) (hB : Continuous B) : Continuous (first B) :=
  continuous_iff_continuousAt.mpr fun t => (first_hasDerivAt B hB t).continuousAt

theorem coning_hasDerivAt (B : ℝ → E) (hB : Continuous B) (t : ℝ) :
    HasDerivAt (coning B)
      ((1/2 : ℝ) • (first B t * B t - B t * first B t)) t := by
  have hc := ((first_continuous B hB).mul hB).sub (hB.mul (first_continuous B hB))
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_smul (1/2 : ℝ)

theorem predictor_hasDerivAt (B : ℝ → E) (hB : Continuous B) (t : ℝ) :
    HasDerivAt (predictor B) ((1 + first B t) * B t) t := by
  have h := first_hasDerivAt B hB t
  convert (((h.const_add 1).add ((h.mul h).const_smul (1/2 : ℝ))).add
    (coning_hasDerivAt B hB t)) using 1
  simp only [add_mul, one_mul, smul_add, smul_sub]
  module

omit [CompleteSpace E] in
@[simp] theorem first_zero (B : ℝ → E) : first B 0 = 0 := by simp [first]
omit [CompleteSpace E] in
@[simp] theorem coning_zero (B : ℝ → E) : coning B 0 = 0 := by simp [coning]
omit [CompleteSpace E] in
@[simp] theorem predictor_zero (B : ℝ → E) : predictor B 0 = 1 := by
  simp [predictor]

/-- The compact quadratic/coning expression is exactly the ordered
approximation through two insertions (three terms including the identity). -/
theorem predictor_eq_approx (B : ℝ → E) (hB : Continuous B) (t : ℝ) :
    predictor B t = Dyson.approx B 3 t := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => predictor_hasDerivAt B hB s)
    (((continuous_const.add (first_continuous B hB)).mul hB).intervalIntegrable 0 t)
  have hp (s : ℝ) : Dyson.approx B 2 s = 1 + first B s := by
    simp [Dyson.approx, first]
  change predictor B t = 1 + ∫ s in (0 : ℝ)..t, Dyson.approx B 2 s * B s
  simp_rw [hp]
  rw [hi, predictor_zero]
  abel

end GNC.OrderedQuadratic
