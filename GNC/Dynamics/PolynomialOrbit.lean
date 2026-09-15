import GNC.Analysis.PolynomialODE
import GNC.Dynamics.GravityField
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A polynomial lift of planar central gravity with tangential thrust.
The fifth state is inverse radius. This is an exact differential identity
away from the gravitational singularity, not a gravity linearization.
-/
namespace GNC.PolynomialOrbit
open PolynomialODE

def field (a : ℚ) : Fin 5 → Expr 5 :=
  let x := Expr.var 0
  let y := Expr.var 1
  let vx := Expr.var 2
  let vy := Expr.var 3
  let u := Expr.var 4
  let u3 := u.multiply (u.multiply u)
  ![vx, vy,
    (u3.multiply x).negate.add ((Expr.constant (-a)).multiply (u.multiply y)),
    (u3.multiply y).negate.add ((Expr.constant a).multiply (u.multiply x)),
    (u3.multiply ((x.multiply vx).add (y.multiply vy))).negate]

noncomputable def rate (a : ℝ) (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![z 2, z 3, -z 4^3*z 0-a*z 4*z 1, -z 4^3*z 1+a*z 4*z 0,
    -z 4^3*(z 0*z 2+z 1*z 3)]

theorem field_correct (a : ℚ) (z : Fin 5 → ℝ) (i : Fin 5) :
    (field a i).value z = rate (a:ℝ) z i := by
  fin_cases i <;> simp [field, Expr.value, rate] <;> ring_nf <;> simp

theorem field_slope {a : ℚ} (ha : |a| ≤ 1/10000) (i : Fin 5) :
    (field a i).slope (4/3) ≤ 32 := by
  fin_cases i <;> norm_num [field, Expr.slope, Expr.majorant, abs_neg] <;> linarith

noncomputable def radius (w : Fin 4 → ℝ) : ℝ := Real.sqrt (w 0^2+w 1^2)

/-- Original planar inverse-square equations with acceleration `a` in the
positive tangential direction. Units are normalized so the gravitational
parameter is one. -/
noncomputable def physicalRate (a : ℝ) (w : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![w 2, w 3, -w 0/(radius w)^3-a*w 1/radius w,
    -w 1/(radius w)^3+a*w 0/radius w]

noncomputable def lift (w : Fin 4 → ℝ) : Fin 5 → ℝ :=
  ![w 0,w 1,w 2,w 3,(radius w)⁻¹]

theorem lift_derivative {w : ℝ → Fin 4 → ℝ} {a t : ℝ}
    (hw : HasDerivAt w (physicalRate a (w t)) t) (hr : 0 < radius (w t)) :
    HasDerivAt (fun s => lift (w s)) (rate a (lift (w t))) t := by
  have h₀ := hasDerivAt_pi.mp hw 0
  have h₁ := hasDerivAt_pi.mp hw 1
  have h₂ := hasDerivAt_pi.mp hw 2
  have h₃ := hasDerivAt_pi.mp hw 3
  simp only [physicalRate, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at h₀ h₁ h₂ h₃
  have hs : w t 0^2+w t 1^2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mp hr)
  have hrad := ((h₀.pow 2).add (h₁.pow 2)).sqrt hs
  have hinv := hrad.inv (ne_of_gt hr)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [lift, rate] using h₀
  · simpa [lift, rate] using h₁
  · convert h₂ using 1
    simp [rate, lift, div_eq_mul_inv]
    ring
  · convert h₃ using 1
    simp [rate, lift, div_eq_mul_inv]
    ring
  · convert hinv using 1
    simp [rate, lift, radius]
    field_simp
    <;> ring

theorem lift_continuous {w : ℝ → Fin 4 → ℝ} (hw : Continuous w)
    (hr : ∀ t, 0 < radius (w t)) : Continuous (fun t => lift (w t)) := by
  have hc : Continuous (fun t => radius (w t)) :=
    Real.continuous_sqrt.comp (((continuous_apply 0).comp hw).pow 2 |>.add
      (((continuous_apply 1).comp hw).pow 2))
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t => w t 0)
    exact (continuous_apply 0).comp hw
  · change Continuous (fun t => w t 1)
    exact (continuous_apply 1).comp hw
  · change Continuous (fun t => w t 2)
    exact (continuous_apply 2).comp hw
  · change Continuous (fun t => w t 3)
    exact (continuous_apply 3).comp hw
  · change Continuous (fun t => (radius (w t))⁻¹)
    exact hc.inv₀ (fun t => ne_of_gt (hr t))

section Lift
noncomputable section
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inverse_radius_derivative {p : ℝ → E} {v : E} {t : ℝ}
    (hp : HasDerivAt p v t) (hz : p t ≠ 0) :
    HasDerivAt (fun s => ‖p s‖⁻¹) (-(‖p t‖⁻¹)^3*⟪p t,v⟫) t := by
  have hn : ‖p t‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  convert (Gravity.norm_derivative hp hz).inv hn using 1
  field_simp

/-- The lifted acceleration has exactly the original gravity and tangential
forcing when `u=1/‖p‖`. A planar quarter-turn supplies `Jp`; normalizing by
radius makes the tangential direction unit length. -/
theorem acceleration_identity (p Jp : E) (a : ℝ) :
    (-(‖p‖⁻¹)^3) • p+(a*‖p‖⁻¹) • Jp =
      Gravity.field 1 p+a • (‖p‖⁻¹ • Jp) := by
  simp only [Gravity.field, smul_smul]
  congr 1
  field_simp

end
end Lift
end GNC.PolynomialOrbit
