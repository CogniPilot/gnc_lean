import GNC.Applications.OrbitalFuel.GravityResponse
import GNC.Applications.OrbitalFuel.PhysicalReferenceEnclosure

/-! Prefix-local forcing bounds for the actual transported gravity remainder.
Clamping extends a continuous forcing beyond the prefix without changing
its original integral. This discharges all regularity outside the prefix
instead of imposing global noncollision on a physical chaser.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPhysical
open GNC PolynomialOrbit PolynomialOrbitTransition Matrix Set
set_option autoImplicit false

def extendForcing (r : ℝ → Vec3) {T : ℝ} (hT : 0 ≤ T) : ℝ → Vec3 :=
  IccExtend hT (fun t => r t.val)

theorem extendForcing_eq (r : ℝ → Vec3) {T : ℝ} (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) : extendForcing r hT t = r t :=
  IccExtend_of_mem hT (fun s => r s.val) ht

theorem extendForcing_continuous (r : ℝ → Vec3) {T : ℝ} (hT : 0 ≤ T)
    (hr : ContinuousOn r (Icc (0:ℝ) T)) : Continuous (extendForcing r hT) :=
  hr.restrict.Icc_extend'

theorem extendForcing_bound (r : ℝ → Vec3) {T R : ℝ} (hT : 0 ≤ T)
    (hb : ∀ t ∈ Icc (0:ℝ) T, GNC.enorm (r t) ≤ R) (t : ℝ) :
    GNC.enorm (extendForcing r hT t) ≤ R :=
  hb (projIcc 0 T hT t).val (projIcc 0 T hT t).property

theorem remainder_congr (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (r s : ℝ → Vec3) {T : ℝ} (hT : 0 ≤ T)
    (he : ∀ t ∈ Icc (0:ℝ) T, r t = s t) (j : Fin 2) :
    remainder F H r T j = remainder F H s T j := by
  have hp : ChaserPrefix.planeRemainder F r T = ChaserPrefix.planeRemainder F s T := by
    unfold ChaserPrefix.planeRemainder
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [he t (by simpa only [uIcc_of_le hT] using ht)]
  have hn : ChaserPrefix.normalRemainder H r T = ChaserPrefix.normalRemainder H s T := by
    unfold ChaserPrefix.normalRemainder
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [he t (by simpa only [uIcc_of_le hT] using ht)]
  unfold remainder
  rw [hp,hn]

/-- The forcing need only be continuous and bounded on the prefix being
certified. The gains hold for its exact position and velocity integrals. -/
theorem gravity_prefix_bound (w : ℝ → Fin 4 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (r : ℝ → Vec3) {R T : ℝ} (hR : 0 ≤ R) (hT : T ∈ Icc (0:ℝ) (3/5))
    (hF : Continuous F) (hH : Continuous H) (hr : ContinuousOn r (Icc (0:ℝ) T))
    (hrad : ∀ t ∈ Icc (0:ℝ) (3/5), 7997/10000 ≤ radius (w t))
    (hdF : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (lift (w t))*F t) t)
    (hdH : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (lift (w t))*H t) t)
    (hiF : F 0 = 1) (hiH : H 0 = 1)
    (hb : ∀ t ∈ Icc (0:ℝ) T, GNC.enorm (r t) ≤ R) :
    GNC.enorm (remainder F H r T 0) ≤ (9/14)*R ∧
    GNC.enorm (remainder F H r T 1) ≤ (15/7)*R := by
  have hg := gravity_response_bound w F H (extendForcing r hT.1) hR hF hH
    (extendForcing_continuous r hT.1 hr) hrad hdF hdH hiF hiH
    (fun s _ => extendForcing_bound r hT.1 hb s) T hT
  have he (j : Fin 2) := remainder_congr F H (extendForcing r hT.1) r hT.1
    (fun s hs => extendForcing_eq r hT.1 hs) j
  rwa [he 0,he 1] at hg

end GNC.Applications.OrbitalFuel.RetainedPhysical
