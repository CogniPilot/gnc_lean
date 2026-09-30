import GNC.Magnus.FohVectorReduction
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Directional derivatives and the rotational semidirect bracket

Every finite rotational bracket expression lifts to pairs of rotation and
velocity vectors. Its velocity component is the directional derivative of its
rotational evaluation, with both generators varied simultaneously.
-/

noncomputable section
namespace GNC.Magnus
open Matrix
open scoped Matrix

/-- The rotation/velocity semidirect bracket. -/
def fohDualBracket (x y : Vec3 × Vec3) : Vec3 × Vec3 :=
  (x.1 ⨯₃ y.1, x.1 ⨯₃ y.2 + x.2 ⨯₃ y.1)

/-- Evaluate a rotational expression in the rotation/velocity semidirect algebra. -/
def FohRotationalExpression.evalDual (a b : Vec3 × Vec3) :
    FohRotationalExpression → Vec3 × Vec3
  | .first => a
  | .second => b
  | .bracket x y => fohDualBracket (x.evalDual a b) (y.evalDual a b)
  | .add x y => x.evalDual a b + y.evalDual a b
  | .scale r x => r • x.evalDual a b

/-- The rotational projection of the semidirect evaluation is the original evaluation. -/
@[simp] theorem FohRotationalExpression.evalDual_fst
    (x : FohRotationalExpression) (a b : Vec3 × Vec3) :
    (x.evalDual a b).1 = x.eval a.1 b.1 := by
  induction x with
  | first => rfl
  | second => rfl
  | bracket x y hx hy => simp [evalDual, eval, fohDualBracket, hx, hy]
  | add x y hx hy => simp [evalDual, eval, hx, hy]
  | scale r x hx => simp [evalDual, eval, hx]

/-- The cross-product rule, in the order used by the semidirect bracket. -/
theorem foh_hasDerivAt_cross {f g : ℝ → Vec3} {df dg : Vec3} {t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) :
    HasDerivAt (fun s => f s ⨯₃ g s) (f t ⨯₃ dg + df ⨯₃ g t) t := by
  have hf' (i : Fin 3) := hasDerivAt_pi.mp hf i
  have hg' (i : Fin 3) := hasDerivAt_pi.mp hg i
  have h (i j : Fin 3) := ((hf' i).mul (hg' j)).sub ((hf' j).mul (hg' i))
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert h 1 2 using 1
    simp [cross_apply]
    ring
  · convert h 2 0 using 1
    simp [cross_apply]
    ring
  · convert h 0 1 using 1
    simp [cross_apply, Matrix.cons_val]
    ring

/-- The chain rule for every finite rotational expression. Only derivatives of
the two input curves are hypotheses; the expression derivative follows by induction. -/
theorem FohRotationalExpression.hasDerivAt_eval
    (x : FohRotationalExpression) {f g : ℝ → Vec3} {df dg : Vec3} {t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) :
    HasDerivAt (fun s => x.eval (f s) (g s))
      (x.evalDual (f t, df) (g t, dg)).2 t := by
  induction x with
  | first => exact hf
  | second => exact hg
  | bracket x y hx hy =>
    simpa only [eval, evalDual, fohDualBracket, evalDual_fst] using
      foh_hasDerivAt_cross hx hy
  | add x y hx hy => exact hx.add hy
  | scale r x hx => exact hx.const_smul r

/-- The universal FOH velocity rule: differentiating both rotational generators
in the velocity directions gives exactly the semidirect velocity evaluation. -/
theorem FohRotationalExpression.hasDerivAt_eval_direction
    (x : FohRotationalExpression) (F G U V : Vec3) :
    HasDerivAt (fun ε : ℝ => x.eval (F + ε • U) (G + ε • V))
      (x.evalDual (F, U) (G, V)).2 0 := by
  have hF : HasDerivAt (fun ε : ℝ => F + ε • U) U 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const U).const_add F
  have hG : HasDerivAt (fun ε : ℝ => G + ε • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add G
  simpa using x.hasDerivAt_eval hF hG

/-- The directional derivative as an equality of vectors. -/
theorem FohRotationalExpression.deriv_eval_direction
    (x : FohRotationalExpression) (F G U V : Vec3) :
    deriv (fun ε : ℝ => x.eval (F + ε • U) (G + ε • V)) 0 =
      (x.evalDual (F, U) (G, V)).2 :=
  (x.hasDerivAt_eval_direction F G U V).deriv

end GNC.Magnus
