import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! Arc and line primitives in physical path distance. These are the
mathematical specification of Planning.Dubins.advance. Selecting a shortest
family and its floating-point evaluation are separate obligations. -/
noncomputable section
namespace GNC.Planning.Dubins
open Real

structure Pose where
  x : ℝ
  y : ℝ
  heading : ℝ

def advance (p : Pose) (k s : ℝ) : Pose where
  x := p.x + if k = 0 then s*cos p.heading else (sin (p.heading+k*s)-sin p.heading)/k
  y := p.y + if k = 0 then s*sin p.heading else (cos p.heading-cos (p.heading+k*s))/k
  heading := p.heading+k*s

theorem advance_zero (p : Pose) (k : ℝ) : advance p k 0 = p := by
  cases p
  simp [advance]

theorem advance_x_derivative (p : Pose) (k s : ℝ) :
    HasDerivAt (fun t => (advance p k t).x) (cos (p.heading+k*s)) s := by
  by_cases hk : k = 0
  · subst k
    simpa [advance] using ((hasDerivAt_id s).mul_const (cos p.heading)).const_add p.x
  · have h := ((((hasDerivAt_id s).const_mul k).const_add p.heading).sin.sub_const
      (sin p.heading)).div_const k
    convert h.const_add p.x using 1 <;> simp [advance, hk]

theorem advance_y_derivative (p : Pose) (k s : ℝ) :
    HasDerivAt (fun t => (advance p k t).y) (sin (p.heading+k*s)) s := by
  by_cases hk : k = 0
  · subst k
    simpa [advance] using ((hasDerivAt_id s).mul_const (sin p.heading)).const_add p.y
  · have h := ((((hasDerivAt_id s).const_mul k).const_add p.heading).cos.const_sub
      (cos p.heading)).div_const k
    convert h.const_add p.y using 1 <;> simp [advance, hk]

theorem advance_heading_derivative (p : Pose) (k s : ℝ) :
    HasDerivAt (fun t => (advance p k t).heading) k s := by
  simpa [advance] using ((hasDerivAt_id s).const_mul k).const_add p.heading

theorem unit_speed (p : Pose) (k s : ℝ) :
    cos (advance p k s).heading ^ 2 + sin (advance p k s).heading ^ 2 = 1 :=
  cos_sq_add_sin_sq _

end GNC.Planning.Dubins
