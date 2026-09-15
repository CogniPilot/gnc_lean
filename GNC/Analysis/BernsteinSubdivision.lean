import GNC.Analysis.BernsteinPolynomial

/-! Finite dyadic refinement of a checked polynomial range. The depth is
an explicit work parameter, not a numerical tolerance. Every leaf interval
is checked, and the original whole-interval bound is retained as a fallback. -/
namespace GNC.BernsteinSubdivision

def bound : ℕ → List ℚ → ℚ → ℚ → ℚ
  | 0,p,lo,hi => BernsteinPolynomial.checked p lo hi
  | n+1,p,lo,hi => min (BernsteinPolynomial.checked p lo hi)
      (max (bound n p lo ((lo+hi)/2)) (bound n p ((lo+hi)/2) hi))

theorem nonnegative (n : ℕ) (p : List ℚ) (lo hi : ℚ) : 0≤bound n p lo hi := by
  induction n generalizing lo hi with
  | zero => exact BernsteinPolynomial.checked_nonnegative p lo hi
  | succ n ih =>
    exact le_min (BernsteinPolynomial.checked_nonnegative p lo hi)
      ((ih lo ((lo+hi)/2)).trans (le_max_left _ _))

theorem no_worse (n : ℕ) (p : List ℚ) (lo hi : ℚ) :
    bound n p lo hi≤BernsteinPolynomial.checked p lo hi := by
  cases n
  · rfl
  · exact min_le_left _ _

theorem sound (n : ℕ) (p : List ℚ) {lo hi : ℚ} (h : lo<hi)
    {x : ℝ} (hx : x ∈ Set.Icc (lo:ℝ) (hi:ℝ)) :
    |PolynomialOrder.value p x|≤(bound n p lo hi:ℝ) := by
  induction n generalizing lo hi with
  | zero => exact BernsteinPolynomial.checked_sound p h hx
  | succ n ih =>
    have hl : lo<(lo+hi)/2 := by linarith
    have hr : (lo+hi)/2<hi := by linarith
    have hw := BernsteinPolynomial.checked_sound p h hx
    have hc : |PolynomialOrder.value p x|≤
        (max (bound n p lo ((lo+hi)/2)) (bound n p ((lo+hi)/2) hi):ℝ) := by
      by_cases hm : x≤(((lo+hi)/2:ℚ):ℝ)
      · exact (ih hl ⟨hx.1,hm⟩).trans (le_max_left _ _)
      · exact (ih hr ⟨(not_le.mp hm).le,hx.2⟩).trans (le_max_right _ _)
    simpa only [bound,Rat.cast_min,Rat.cast_max] using le_min hw hc

end GNC.BernsteinSubdivision
