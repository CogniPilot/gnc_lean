import GNC.Dynamics.PlanarGravityFlow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The physical radial/tangential/normal frame along the planar thrusting
reference. Positive angular momentum fixes the normal orientation; the
inverse-radius lift makes the frame entries polynomial.
-/
noncomputable section
namespace GNC.PolynomialOrbitTransition
open PolynomialOrbit Matrix
open scoped Matrix

def velocity (w : Fin 4 → ℝ) : Vec3 := ![w 2,w 3,0]
def angularMomentum (w : Fin 4 → ℝ) : ℝ := w 0*w 3-w 1*w 2

theorem radius_sq (w : Fin 4 → ℝ) : (radius w)^2 = w 0^2+w 1^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem angularMomentum_derivative {w : ℝ → Fin 4 → ℝ} {a t : ℝ}
    (hw : HasDerivAt w (physicalRate a (w t)) t) (hr : 0 < radius (w t)) :
    HasDerivAt (fun s => angularMomentum (w s)) (a*radius (w t)) t := by
  have h0 := hasDerivAt_pi.mp hw 0
  have h1 := hasDerivAt_pi.mp hw 1
  have h2 := hasDerivAt_pi.mp hw 2
  have h3 := hasDerivAt_pi.mp hw 3
  simp [physicalRate] at h0 h1 h2 h3
  have h := (h0.mul h3).sub (h1.mul h2)
  convert h using 1
  change a*radius (w t) = _
  symm
  calc
    _ = a/radius (w t)*(w t 0^2+w t 1^2) := by ring
    _ = a*radius (w t) := by rw [← radius_sq]; field_simp

theorem angularMomentum_positive (w : ℝ → Fin 4 → ℝ) {a T : ℝ}
    (hw : Continuous w) (ha : 0 ≤ a)
    (hr : ∀ t ∈ Set.Icc (0:ℝ) T, 0 < radius (w t))
    (hd : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt w (physicalRate a (w t)) t)
    (hi : 0 < angularMomentum (w 0)) :
    ∀ t ∈ Set.Icc (0:ℝ) T, 0 < angularMomentum (w t) := by
  have hc : Continuous (fun s => angularMomentum (w s)) :=
    (((continuous_apply 0).comp hw).mul ((continuous_apply 3).comp hw)).sub
      (((continuous_apply 1).comp hw).mul ((continuous_apply 2).comp hw))
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) T) hc.continuousOn
    (fun t ht => (angularMomentum_derivative (hd t (interior_subset ht))
      (hr t (interior_subset ht))).hasDerivWithinAt)
    (fun t ht => mul_nonneg ha (hr t (interior_subset ht)).le)
  intro t ht
  exact hi.trans_le (hm ⟨le_rfl,ht.1.trans ht.2⟩ ht ht.1)

theorem cross_position_velocity (w : Fin 4 → ℝ) :
    position w ⨯₃ velocity w = ![0,0,angularMomentum w] := by
  ext i
  fin_cases i <;> simp [position, velocity, angularMomentum, cross_apply]

theorem enorm_cross (w : Fin 4 → ℝ) :
    enorm (position w ⨯₃ velocity w) = |angularMomentum w| := by
  rw [cross_position_velocity]
  have hs := enorm_sq (![0,0,angularMomentum w])
  simp [lengthSq] at hs
  change enorm (![0,0,angularMomentum w])^2 = angularMomentum w^2 at hs
  nlinarith [enorm_nonneg (![0,0,angularMomentum w]), abs_nonneg (angularMomentum w),
    sq_abs (angularMomentum w)]

def unitNormal (w : Fin 4 → ℝ) : Vec3 :=
  (enorm (position w ⨯₃ velocity w))⁻¹ • (position w ⨯₃ velocity w)

theorem unitNormal_positive (w : Fin 4 → ℝ) (hh : 0 < angularMomentum w) :
    unitNormal w = ![0,0,1] := by
  rw [unitNormal, enorm_cross, cross_position_velocity, abs_of_pos hh]
  ext i
  fin_cases i <;> simp [hh.ne']

def physicalFrame (w : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let er := (enorm (position w))⁻¹ • position w
  let en := unitNormal w
  let et := en ⨯₃ er
  fun i j => ![er i,et i,en i] j

def polynomialFrame (z : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![z 0*z 4,-z 1*z 4,0; z 1*z 4,z 0*z 4,0; 0,0,1]

theorem physicalFrame_eq (w : Fin 4 → ℝ) (hh : 0 < angularMomentum w) :
    physicalFrame w = polynomialFrame (lift w) := by
  unfold physicalFrame
  rw [position_norm, unitNormal_positive w hh]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [polynomialFrame, lift, position, cross_apply] <;> ring

end GNC.PolynomialOrbitTransition
