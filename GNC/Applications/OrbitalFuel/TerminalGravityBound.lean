import GNC.Applications.OrbitalFuel.ValidatedTerminalGravity
import GNC.Applications.OrbitalFuel.TerminalGravityGeometry

/-! The six checked transport gains bound the actual terminal remainder
for every bounded forcing, including state-dependent gravity errors.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.TerminalGravity
open GNC PolynomialOrbitTransition PolynomialBurn Matrix MeasureTheory Set

theorem unitScale_nonneg {speed : ℝ} (hs : 0 ≤ speed) (i : Fin 6) : 0 ≤ unitScale speed i := by
  fin_cases i <;> simp [unitScale, FreeResponse.lengthUnit, FreeResponse.tolerance] <;> positivity

theorem euclidean_pairing (a b : Vec3) :
    inner ℝ (ThrustSupport.euclideanEquiv a) (ThrustSupport.euclideanEquiv b) = a ⬝ᵥ b := by
  change (∑ k : Fin 3, b k*a k) = ∑ k : Fin 3, a k*b k
  simp only [mul_comm]

theorem remainder_bound (x : Trajectory) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hx : x.state = fun t => pack (z t) (F t) (H t))
    (hF : Continuous F) (hH : Continuous H) (r : ℝ → Vec3)
    (hr : ContinuousOn r (Icc (0:ℝ) (3/5))) {R speed : ℝ}
    (hR : 0 ≤ R) (hs : 0 ≤ speed)
    (hb : ∀ t ∈ Icc (0:ℝ) (3/5), GNC.enorm (r t) ≤ R) (i : Fin 6) :
    |TerminalResponse.output (z (3/5)) speed (ChaserResponse.planeRemainder F r)
      (ChaserResponse.normalRemainder H r) i| ≤ unitScale speed i*(gain i:ℝ)*R := by
  have h := PolynomialNormIntegral.forced_pairing
    (fun t => ThrustSupport.euclideanEquiv (kernel x i t))
    (fun t => ThrustSupport.euclideanEquiv (r t))
    (by norm_num : (0:ℝ) ≤ 3/5)
    ((ThrustSupport.euclideanEquiv.continuous.comp (kernel_continuous x i)).continuousOn)
    (ThrustSupport.euclideanEquiv.continuous.comp_continuousOn hr) hR hb (norm_integral x i)
  simp_rw [euclidean_pairing] at h
  rw [output_scale, abs_mul, abs_of_nonneg (unitScale_nonneg hs i),
    remainder_pairing x z F H hx hF hH r hr i]
  exact (mul_le_mul_of_nonneg_left h (unitScale_nonneg hs i)).trans (le_of_eq (by ring))

end GNC.Applications.OrbitalFuel.TerminalGravity
