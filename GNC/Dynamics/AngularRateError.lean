import GNC.Control.LogBackstepping

/-! Exact angular-rate augmentation of a geometric configuration error.
Angular velocity is a dynamical state, not an extra translational column of
SE_2(3). Its Euler equation retains a reference-dependent linear part and a
quadratic gyroscopic residual. No torque cancellation is assumed here.
-/
noncomputable section
open Matrix
namespace GNC.AngularRateError

/-- Reference-dependent linear gyroscopic terms plus the exact quadratic
remainder. The reference rate must be expressed in the same body frame. -/
theorem gyroscopic_split (I : Vec3 →ₗ[ℝ] Vec3) (wref z : Vec3) :
    (wref+z) ⨯₃ I (wref+z)-wref ⨯₃ I wref =
      wref ⨯₃ I z+z ⨯₃ I wref+z ⨯₃ I z := by
  simp only [map_add, LinearMap.add_apply]
  abel

/-- Actual rate-error derivative around any differentiable virtual rate.
The reference torque defect is explicit. This applies to a PID as well as
to an inversion controller and does not assume instantaneous rate tracking. -/
theorem derivative (I : Vec3 ≃ₗ[ℝ] Vec3)
    {w wref : ℝ → Vec3} {τ τref dwref : Vec3} {t : ℝ}
    (hw : HasDerivAt w (I.symm (τ-w t ⨯₃ I (w t))) t)
    (href : HasDerivAt wref dwref t) :
    HasDerivAt (fun s => w s-wref s)
      (I.symm (τ-τref-
        (wref t ⨯₃ I (w t-wref t)+(w t-wref t) ⨯₃ I (wref t))-
        (w t-wref t) ⨯₃ I (w t-wref t))+
        (I.symm (τref-wref t ⨯₃ I (wref t))-dwref)) t := by
  have h := gyroscopic_split I.toLinearMap (wref t) (w t-wref t)
  simp only [add_sub_cancel] at h
  have he : w t ⨯₃ I (w t) =
      wref t ⨯₃ I (w t-wref t)+(w t-wref t) ⨯₃ I (wref t)+
        (w t-wref t) ⨯₃ I (w t-wref t)+wref t ⨯₃ I (wref t) :=
    (sub_eq_iff_eq_add).mp h
  convert hw.sub href using 1
  rw [he]
  simp only [map_sub, map_add]
  abel

/-- The quadratic gyroscopic remainder is exactly neutral in the inertia
energy. Bounding its norm would lose this cancellation. A general dense
metric, including cross blocks, must account for its pairing separately. -/
theorem quadratic_residual_neutral (I : Vec3 ≃ₗ[ℝ] Vec3) (z : Vec3) :
    z ⬝ᵥ I (I.symm (-(z ⨯₃ I z))) = 0 := by
  simp

/-- The same-frame reference term z cross I*wref is also neutral; the
remaining wref cross I*z term can transfer error energy. -/
theorem gyroscopic_energy_split (I : Vec3 →ₗ[ℝ] Vec3) (wref z : Vec3) :
    z ⬝ᵥ ((wref+z) ⨯₃ I (wref+z)-wref ⨯₃ I wref) =
      z ⬝ᵥ (wref ⨯₃ I z) := by
  rw [gyroscopic_split]
  simp

end GNC.AngularRateError
