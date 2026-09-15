import GNC.Applications.OrbitalFuel.ReferenceEnvelopes
import GNC.Applications.OrbitalFuel.PolynomialTransition
import GNC.Dynamics.PlanarChaserError
import GNC.Control.ThrustIntegral

/-! Apply the orbital-invariant annulus theorem to the exact four-component
solar reference used by the validated transition and fuel certificates.
The unit-thrust direction and Cartesian derivative identities are proved
from the physical reference equations, not supplied as correspondence assumptions.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.Reference
open GNC GNC.ThrustSupport PolynomialOrbit PolynomialOrbitTransition Matrix Set
open scoped RealInnerProductSpace
set_option autoImplicit false

def tangent (w : Fin 4 → ℝ) : Vec3 := ![-w 1/radius w,w 0/radius w,0]

theorem tangent_norm (w : Fin 4 → ℝ) (hr : 0 < radius w) : GNC.enorm (tangent w) = 1 := by
  have hs := enorm_sq (tangent w)
  have hl : lengthSq (tangent w) = 1 := by
    change (-w 1/radius w)^2+(w 0/radius w)^2+(0:ℝ)^2 = 1
    rw [zero_pow (by decide : 2 ≠ 0),add_zero]
    field_simp
    nlinarith [radius_sq w]
  rw [hl] at hs
  nlinarith [enorm_nonneg (tangent w)]

theorem tangent_bound (w : Fin 4 → ℝ) : GNC.enorm (tangent w) ≤ 1 := by
  by_cases hr : radius w = 0
  · have he : tangent w = 0 := by
      ext i
      fin_cases i <;> simp [tangent,hr,Matrix.cons_val_two]
    rw [he]
    change ‖(0 : Jacobian.E3)‖ ≤ 1
    norm_num
  · rw [tangent_norm w (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr))]

theorem thrust_tangent (α : ℝ) (w : Fin 4 → ℝ) :
    PlanarChaserError.referenceThrust α w = α • tangent w := by
  ext i
  fin_cases i <;>
    simp [PlanarChaserError.referenceThrust,polynomialFrame,lift,tangent,div_eq_mul_inv]

theorem position_derivative {w : ℝ → Fin 4 → ℝ} {α t : ℝ}
    (hw : HasDerivAt w (physicalRate α (w t)) t) :
    HasDerivAt (fun s => position (w s)) (velocity (w t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [position,velocity,physicalRate] using hasDerivAt_pi.mp hw 0
  · simpa [position,velocity,physicalRate] using hasDerivAt_pi.mp hw 1
  · simpa [position,velocity] using hasDerivAt_const t (0:ℝ)

theorem velocity_derivative {w : ℝ → Fin 4 → ℝ} {α t : ℝ}
    (hw : HasDerivAt w (physicalRate α (w t)) t) :
    HasDerivAt (fun s => velocity (w s))
      (Gravity.field3 1 (position (w t))+α • tangent (w t)) t := by
  rw [← thrust_tangent,← PlanarChaserError.reference_acceleration]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [velocity] using hasDerivAt_pi.mp hw 2
  · simpa [velocity] using hasDerivAt_pi.mp hw 3
  · simpa [velocity,Matrix.cons_val_two] using hasDerivAt_const t (0:ℝ)

theorem physical_solar_annulus (w : ℝ → Fin 4 → ℝ) (hw : Continuous w)
    (hd : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt w
      (physicalRate (PolynomialTransition.alpha:ℝ) (w t)) t)
    (hi : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) :
    ∀ t ∈ Icc (0:ℝ) (3/5),
      7997/10000 < radius (w t) ∧ radius (w t) < 2401/2000 ∧
        GNC.enorm (velocity (w t)) < 613/500 := by
  have hp : Continuous (fun t => position (w t)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [position,Matrix.cons_val_two] <;> fun_prop
  have hv : Continuous (fun t => velocity (w t)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [velocity,Matrix.cons_val_two] <;> fun_prop
  have hα : (PolynomialTransition.alpha:ℝ) = solarThrust := by
    norm_num [PolynomialTransition.alpha,solarThrust,solarLength,solarMu]
  have h := solar_annulus (fun t => euclideanEquiv (position (w t)))
    (fun t => euclideanEquiv (velocity (w t))) (fun t => euclideanEquiv (tangent (w t)))
    (euclideanEquiv.continuous.comp hp) (euclideanEquiv.continuous.comp hv)
    (fun t ht => euclideanEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (position_derivative (hd t ht))) (by
      intro t ht
      have hh := euclideanEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
        (velocity_derivative (hd t ht))
      simpa only [hα,map_add,map_smul] using hh)
    (fun t _ => tangent_bound (w t)) (by
      change GNC.enorm (position (w 0)) = _
      rw [position_norm,hi]
      norm_num [radius]) (by
      change GNC.enorm (velocity (w 0))^2 = _
      rw [enorm_sq,hi]
      change (0:ℝ)^2+(Real.sqrt (3/2:ℝ))^2+(0:ℝ)^2 = 3/2
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/2)]) (by
      change inner ℝ (WithLp.toLp 2 (position (w 0)) : Jacobian.E3)
        (WithLp.toLp 2 (velocity (w 0))) = 0
      rw [Gravity.inner_toLp,hi]
      simp [position,velocity,dotProduct,Fin.sum_univ_succ])
  simpa only [show ∀ z : Vec3, ‖euclideanEquiv z‖ = GNC.enorm z from fun _ => rfl,
    position_norm] using h

end GNC.Applications.OrbitalFuel.Reference
