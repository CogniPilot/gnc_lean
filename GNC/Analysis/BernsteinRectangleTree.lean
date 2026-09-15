import GNC.Analysis.BivariateBernstein

/-! A finite adaptive rectangle cover with independently reconstructed
Bernstein leaves. The proposal's branching and stopping decisions are not
trusted; the checker covers both children of every split. -/
namespace GNC.BernsteinRectangleTree
open BivariatePolynomial

inductive Tree (n m : ℕ) where
  | leaf (coefficients : Fin (n+1) → Fin (m+1) → ℚ)
  | splitX (left right : Tree n m)
  | splitY (left right : Tree n m)

def check {n m : ℕ} (p : Coefficients) (upper : ℚ) :
    Tree n m → ℚ → ℚ → ℚ → ℚ → Bool
  | .leaf b, lo, hi, bot, top => decide
      (BivariateBernstein.valid p lo hi bot top n m b ∧ ∀ i j, b i j ≤ upper)
  | .splitX l r, lo, hi, bot, top =>
      check p upper l lo ((lo+hi)/2) bot top && check p upper r ((lo+hi)/2) hi bot top
  | .splitY l r, lo, hi, bot, top =>
      check p upper l lo hi bot ((bot+top)/2) && check p upper r lo hi ((bot+top)/2) top

theorem check_sound {n m : ℕ} (p : Coefficients) (upper : ℚ) (tree : Tree n m)
    {lo hi bot top : ℚ} (hx : lo < hi) (hy : bot < top)
    (hc : check p upper tree lo hi bot top = true)
    {u v : ℝ} (hu : u ∈ Set.Icc (lo:ℝ) hi) (hv : v ∈ Set.Icc (bot:ℝ) top) :
    value p u v ≤ (upper:ℝ) := by
  induction tree generalizing lo hi bot top with
  | leaf b =>
    have h := of_decide_eq_true hc
    exact BivariateBernstein.valid_upper p hx hy n m b h.1 h.2 hu hv
  | splitX l r hl hr =>
    have h := Bool.and_eq_true_iff.mp hc
    rcases le_total u (((lo+hi)/2:ℚ):ℝ) with hleft | hright
    · exact hl (by linarith : lo < (lo+hi)/2) hy h.1 ⟨hu.1,hleft⟩ hv
    · exact hr (by linarith : (lo+hi)/2 < hi) hy h.2 ⟨hright,hu.2⟩ hv
  | splitY l r hl hr =>
    have h := Bool.and_eq_true_iff.mp hc
    rcases le_total v (((bot+top)/2:ℚ):ℝ) with hleft | hright
    · exact hl hx (by linarith : bot < (bot+top)/2) h.1 hu ⟨hv.1,hleft⟩
    · exact hr hx (by linarith : (bot+top)/2 < top) h.2 hu ⟨hright,hv.2⟩

end GNC.BernsteinRectangleTree
