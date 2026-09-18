import GNC.Analysis.PolynomialForcing

/-! Rationally checkable envelopes with nonzero initial radii. -/
namespace GNC.InitialPolynomialForcing
open Planning.PolynomialKernel PolynomialOrder Set

structure Valid (κ p₀ v₀ : ℚ) (f p : List ℚ) : Prop where
  position_nonnegative : nonnegative p
  velocity_nonnegative : nonnegative (differentiate p)
  position_initial : evaluate p 0=p₀
  velocity_initial : evaluate (differentiate p) 0=v₀
  differential : prefixes 0 (PolynomialBounds.subtract (differentiate (differentiate p))
    (PolynomialBounds.add (PolynomialBounds.scale κ p) f))

instance (κ p₀ v₀ : ℚ) (f p : List ℚ) : Decidable (Valid κ p₀ v₀ f p) := by
  refine decidable_of_iff (nonnegative p ∧ nonnegative (differentiate p) ∧
    evaluate p 0=p₀ ∧ evaluate (differentiate p) 0=v₀ ∧
    prefixes 0 (PolynomialBounds.subtract (differentiate (differentiate p))
      (PolynomialBounds.add (PolynomialBounds.scale κ p) f))) ?_
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,
    fun h => ⟨h.position_nonnegative,h.velocity_nonnegative,h.position_initial,
      h.velocity_initial,h.differential⟩⟩

theorem supersolution {κ p₀ v₀ : ℚ} {f p : List ℚ} (hp : Valid κ p₀ v₀ f p)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (κ:ℝ)*value p t+value f t≤value (differentiate (differentiate p)) t := by
  have h := prefixes_sound _ hp.differential ht
  simpa only [value_subtract,value_add,value_scale,sub_nonneg] using h

theorem initial {κ p₀ v₀ : ℚ} {f p : List ℚ} (hp : Valid κ p₀ v₀ f p) :
    value p 0=(p₀:ℝ) ∧ value (differentiate p) 0=(v₀:ℝ) := by
  have hP := value_at_rational p 0
  have hV := value_at_rational (differentiate p) 0
  simpa only [Rat.cast_zero,hp.position_initial,hp.velocity_initial] using And.intro hP hV

end GNC.InitialPolynomialForcing
