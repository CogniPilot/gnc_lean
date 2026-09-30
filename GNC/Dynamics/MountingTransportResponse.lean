import GNC.Dynamics.MountingTransportFlow
import GNC.Dynamics.ReactionWheels
import GNC.Control.ThrustIntegral

/-! An input-to-state bound for exact mounting-frame transport, derived
from its ODE. The bound contains no accumulated angular-rate factor.
It does not remove the gravity or kinematic couplings of an orbital ODE.
-/
noncomputable section
open Set MeasureTheory
namespace GNC.MountingTransportFlow
open Matrix Real MountingErrorCoordinates
open scoped Matrix.Norms.Operator

theorem physical_derivative (φ : Vec3) (hφ : enorm φ<2*π)
    {R : ℝ → SO3} {x : ℝ → Vec3} {ω f : Vec3} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*skew ω) t)
    (hx : HasDerivAt x (-transport φ ω (x t)+f) t) :
    HasDerivAt (fun s => rotate (R s) (Jacobian.leftAt φ (x s)))
      (rotate (R t) (Jacobian.leftAt φ f)) t := by
  have hj : HasDerivAt (fun s => Jacobian.leftAt φ (x s))
      (Jacobian.leftAt φ (-transport φ ω (x t)+f)) t := by
    simpa only [jacobianMatrix_mulVec, Matrix.zero_mulVec, zero_add] using
      SymplecticResponse.mulVec_derivative (hasDerivAt_const t (jacobianMatrix φ)) hx
  convert ReactionWheels.rotate_derivative hR hj using 1
  congr 1
  have hneg (y : Vec3) : Jacobian.leftAt φ (-y) = -Jacobian.leftAt φ y := by
    simp only [Jacobian.leftAt, map_neg]
    module
  rw [Jacobian.leftAt_add, hneg, transport, Jacobian.leftAt_inverseAt_all φ _ hφ]
  abel

/-- Exact cancellation of frame transport gives an integral gain bound.
Inputs need only be continuous; rates may vary arbitrarily. In physical
norm the gain is one; returning to log translation costs at most 4/3 on
the one-radian mounting ball, independently of the number of revolutions. -/
theorem forced_bound (φ : Vec3) (hφ : enorm φ≤1)
    (R : ℝ → SO3) (ω x f : ℝ → Vec3) {T : ℝ} (hT : 0≤T)
    (hR : ∀ t, HasDerivAt (fun s => (R s).val) ((R t).val*skew (ω t)) t)
    (hx : ∀ t ∈ Icc 0 T, HasDerivAt x (-transport φ (ω t) (x t)+f t) t)
    (hf : Continuous f) :
    physicalNorm φ (x T)≤physicalNorm φ (x 0)+(∫ t in 0..T, enorm (f t)) ∧
    enorm (x T)≤(4/3:ℝ)*(enorm (x 0)+(∫ t in 0..T, enorm (f t))) := by
  have hchart : enorm φ<2*π := by linarith [pi_gt_three]
  let u := fun t => rotate (R t) (Jacobian.leftAt φ (f t))
  have hRc : Continuous (fun t => (R t).val) :=
    continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt
  have hu : Continuous u := by
    dsimp [u, rotate]
    simp only [←jacobianMatrix_mulVec]
    fun_prop
  have hnu : Continuous (fun t => enorm (u t)) :=
    (ThrustSupport.euclideanEquiv.continuous.comp hu).norm
  have hnf : Continuous (fun t => enorm (f t)) :=
    (ThrustSupport.euclideanEquiv.continuous.comp hf).norm
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => physical_derivative φ hchart (hR t)
      (hx t (by simpa [uIcc_of_le hT] using ht)))
    (hu.intervalIntegrable (μ := volume) 0 T)
  change (∫ t in 0..T, u t)=
    rotate (R T) (Jacobian.leftAt φ (x T))-
      rotate (R 0) (Jacobian.leftAt φ (x 0)) at he
  have hid := (sub_eq_iff_eq_add.mp he.symm)
  have hb := enorm_add_le (∫ t in 0..T, u t)
    (rotate (R 0) (Jacobian.leftAt φ (x 0)))
  rw [←hid, rotate_enorm, rotate_enorm] at hb
  have hi := ThrustSupport.enorm_integral_le u hT (hu.intervalIntegrable 0 T)
  have hmono := intervalIntegral.integral_mono_on hT
    (hnu.intervalIntegrable (μ := volume) 0 T) (hnf.intervalIntegrable (μ := volume) 0 T)
    (fun t _ => show enorm (u t)≤enorm (f t) by
      rw [show enorm (u t)=enorm (Jacobian.leftAt φ (f t)) from rotate_enorm _ _]
      exact leftAt_nonexpansive φ (f t) hchart)
  have hp : physicalNorm φ (x T)≤physicalNorm φ (x 0)+(∫ t in 0..T, enorm (f t)) := by
    dsimp [physicalNorm]
    linarith
  refine ⟨hp,?_⟩
  have hj := inverse_bound φ (Jacobian.leftAt φ (x T)) hφ
  rw [Jacobian.inverseAt_leftAt_all φ _ hchart] at hj
  have h0 := leftAt_nonexpansive φ (x 0) hchart
  dsimp [physicalNorm] at hp
  linarith

end GNC.MountingTransportFlow
