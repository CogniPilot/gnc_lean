import GNC.Analysis.PolynomialOrder

/-! A checked polynomial supersolution for a polynomial forcing profile and
an arbitrary nonnegative gain. The certificate includes zero initial error
and slope. Prefix checks use the full unit interval, with no inflation term. -/
namespace GNC.PolynomialForcing
open Planning.PolynomialKernel PolynomialOrder Set

def Valid (κ : ℚ) (forcing envelope : List ℚ) : Prop :=
  nonnegative forcing ∧ nonnegative envelope ∧ nonnegative (differentiate envelope) ∧
  evaluate envelope 0=0 ∧ evaluate (differentiate envelope) 0=0 ∧
  prefixes 0 (PolynomialBounds.subtract (differentiate (differentiate envelope))
    (PolynomialBounds.add (PolynomialBounds.scale κ envelope) forcing))

instance (κ : ℚ) (f p : List ℚ) : Decidable (Valid κ f p) := by
  unfold Valid
  infer_instance

theorem supersolution (κ : ℚ) (f p : List ℚ) (hp : Valid κ f p) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    (κ:ℝ)*value p t+value f t≤value (differentiate (differentiate p)) t := by
  have h := prefixes_sound _ hp.2.2.2.2.2 ht
  simpa only [value_subtract,value_add,value_scale,sub_nonneg] using h

theorem initial (κ : ℚ) (f p : List ℚ) (hp : Valid κ f p) :
    value p 0=0 ∧ value (differentiate p) 0=0 := by
  have hP := value_at_rational p 0
  have hV := value_at_rational (differentiate p) 0
  simpa only [Rat.cast_zero,hp.2.2.2.1,hp.2.2.2.2.1] using And.intro hP hV

end GNC.PolynomialForcing
