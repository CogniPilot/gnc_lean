import GNC.Analysis.PolynomialODE
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! An executable, all-order Lie-derivative recurrence for polynomial ODEs.
The coefficients use only the field and the initial state. The theorem
identifies them with actual trajectory derivatives on any open solution
interval. Summability/analyticity is a separate obligation: this module
does not turn a formal series into a convergent solution by definition.
-/
namespace GNC.PolynomialODE.Expr
variable {n : ℕ}

def lieDerivative (f : Fin n → Expr n) : Expr n → Expr n
  | .constant _ => .constant 0
  | .var i => f i
  | .add a b => .add (lieDerivative f a) (lieDerivative f b)
  | .multiply a b => .add (.multiply (lieDerivative f a) b)
      (.multiply a (lieDerivative f b))
  | .negate a => .negate (lieDerivative f a)

def lieIterate (f : Fin n → Expr n) : ℕ → Expr n → Expr n
  | 0, e => e
  | k+1, e => lieDerivative f (lieIterate f k e)

theorem lieDerivative_correct (f : Fin n → Expr n) (e : Expr n)
    {z : ℝ → Fin n → ℝ} {t : ℝ}
    (hz : HasDerivAt z (fun i => (f i).value (z t)) t) :
    HasDerivAt (fun s => e.value (z s)) ((lieDerivative f e).value (z t)) t := by
  induction e with
  | constant c => simpa [lieDerivative, value] using hasDerivAt_const t (c:ℝ)
  | var i => exact hasDerivAt_pi.mp hz i
  | add a b ha hb => exact ha.add hb
  | multiply a b ha hb => exact ha.mul hb
  | negate a ha => exact ha.neg

/-- Every coefficient of the Lie series is determined by the prescribed
polynomial field and one state evaluation, with no unknown time-history
integral. A clock and polynomial input states may be included in z. -/
theorem lieIterate_derivative (f : Fin n → Expr n) (e : Expr n)
    {z : ℝ → Fin n → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hz : ∀ t ∈ S, HasDerivAt z (fun i => (f i).value (z t)) t)
    (k : ℕ) {t : ℝ} (ht : t ∈ S) :
    iteratedDeriv k (fun s => e.value (z s)) t = (lieIterate f k e).value (z t) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : (fun s => (lieIterate f k e).value (z s)) =ᶠ[nhds t]
        iteratedDeriv k (fun s => e.value (z s)) := by
      filter_upwards [hS.mem_nhds ht] with s hs
      exact (ih hs).symm
    exact ((lieDerivative_correct f (lieIterate f k e) (hz t ht)).congr_of_eventuallyEq
      he.symm).deriv

end GNC.PolynomialODE.Expr
