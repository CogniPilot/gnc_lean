import GNC.Applications.OrbitalFuel.PhysicalPrefixEnclosure
import GNC.Analysis.SymplecticForcedResponse
import GNC.Analysis.SecondOrderBound
import GNC.Dynamics.GravityGradientBound
import GNC.Control.ThrustIntegral
import Mathlib.Topology.Order.ProjIcc

/-! Continuous gravity-response gains for the actual integral remainder.
The reference-dependent central-gravity generator is retained. No sampled
transition norm or assumed error differential equation enters the bound.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPhysical
open GNC GNC.ThrustSupport PolynomialOrbit PolynomialOrbitTransition PlanarChaserError
open RetainedPrefix Matrix Set
set_option autoImplicit false

theorem remainder_position (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ → Vec3) (t : ℝ) :
    remainder F H r t 0 =
      ![ChaserPrefix.planeRemainder F r t 0,ChaserPrefix.planeRemainder F r t 1,
        ChaserPrefix.normalRemainder H r t 0] := by
  ext i
  fin_cases i <;> rfl

theorem remainder_velocity (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ → Vec3) (t : ℝ) :
    remainder F H r t 1 =
      ![ChaserPrefix.planeRemainder F r t 2,ChaserPrefix.planeRemainder F r t 3,
        ChaserPrefix.normalRemainder H r t 1] := by
  ext i
  fin_cases i <;> rfl

theorem remainder_initial (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ → Vec3) (j : Fin 2) :
    remainder F H r 0 j = 0 := by
  ext i
  simp [remainder,ChaserPrefix.planeRemainder,ChaserPrefix.normalRemainder,
    cartesian,show (![0,0,0,0,0,0] : Fin 6 → ℝ) = 0 by ext k; fin_cases k <;> rfl]

theorem planeInput_continuous : Continuous planeInput := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [planeInput,Matrix.cons_val_two,Matrix.cons_val_three] <;> fun_prop

theorem normalInput_continuous : Continuous normalInput := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [normalInput] <;> fun_prop

theorem remainder_continuous (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ → Vec3)
    (hF : Continuous F) (hH : Continuous H) (hr : Continuous r) (j : Fin 2) :
    Continuous (fun t => remainder F H r t j) := by
  have hp : Continuous (ChaserPrefix.planeRemainder F r) :=
    SymplecticResponse.forced_continuous F planeForm (fun t => planeInput (r t))
      hF (planeInput_continuous.comp hr)
  have hn : Continuous (ChaserPrefix.normalRemainder H r) :=
    SymplecticResponse.forced_continuous H normalForm (fun t => normalInput (r t))
      hH (normalInput_continuous.comp hr)
  fin_cases j <;> apply continuous_pi <;> intro i <;> fin_cases i
  · exact (continuous_apply (0 : Fin 4)).comp hp
  · exact (continuous_apply (1 : Fin 4)).comp hp
  · exact (continuous_apply (0 : Fin 2)).comp hn
  · exact (continuous_apply (2 : Fin 4)).comp hp
  · exact (continuous_apply (3 : Fin 4)).comp hp
  · exact (continuous_apply (1 : Fin 2)).comp hn

/-- The two Cartesian output blocks solve the genuine second-order gravity
equation. Invertibility follows from the initialized Hamiltonian flow. -/
theorem remainder_derivatives (w : ℝ → Fin 4 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (r : ℝ → Vec3) {T : ℝ}
    (hF : Continuous F) (hH : Continuous H) (hr : Continuous r)
    (hdF : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt F (planeGenerator (lift (w t))*F t) t)
    (hdH : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt H (normalGenerator (lift (w t))*H t) t)
    (hiF : F 0 = 1) (hiH : H 0 = 1) {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    HasDerivAt (fun s => remainder F H r s 0) (remainder F H r t 1) t ∧
    HasDerivAt (fun s => remainder F H r s 1)
      (Gravity.gradient3 1 (position (w t)) (remainder F H r t 0)+r t) t := by
  have hp := SymplecticResponse.forced_derivative F
    (fun s => planeGenerator (lift (w s))) planeForm (fun s => planeInput (r s))
    hF (planeInput_continuous.comp hr) planeForm_sq hdF
    (fun s _ => plane_hamiltonian (lift (w s))) hiF ht
  have hn := SymplecticResponse.forced_derivative H
    (fun s => normalGenerator (lift (w s))) normalForm (fun s => normalInput (r s))
    hH (normalInput_continuous.comp hr) normalForm_sq hdH
    (fun s _ => normal_hamiltonian (lift (w s))) hiH ht
  change HasDerivAt (ChaserPrefix.planeRemainder F r)
    (planeGenerator (lift (w t))*ᵥ ChaserPrefix.planeRemainder F r t+planeInput (r t)) t at hp
  change HasDerivAt (ChaserPrefix.normalRemainder H r)
    (normalGenerator (lift (w t))*ᵥ ChaserPrefix.normalRemainder H r t+normalInput (r t)) t at hn
  rw [plane_action (w t) _ (ChaserPrefix.normalRemainder H r t 0)] at hp
  rw [normal_action (w t) _ (ChaserPrefix.planeRemainder F r t 0)
    (ChaserPrefix.planeRemainder F r t 1)] at hn
  simp only [remainder_position,remainder_velocity]
  constructor <;> apply hasDerivAt_pi.mpr <;> intro i <;> fin_cases i
  · simpa [planeInput] using hasDerivAt_pi.mp hp 0
  · simpa [planeInput] using hasDerivAt_pi.mp hp 1
  · simpa [normalInput] using hasDerivAt_pi.mp hn 0
  · simpa [planeInput,Matrix.cons_val_two] using hasDerivAt_pi.mp hp 2
  · simpa [planeInput,Matrix.cons_val_three] using hasDerivAt_pi.mp hp 3
  · simpa [normalInput,Matrix.cons_val_two] using hasDerivAt_pi.mp hn 1

theorem gradient_four (w : Fin 4 → ℝ) (x : Vec3)
    (hr : 7997/10000 ≤ radius w) :
    GNC.enorm (Gravity.gradient3 1 (position w) x) ≤ 4*GNC.enorm x := by
  have hc : (7997/10000:ℝ)^3 ≤ (radius w)^3 := by gcongr
  have hp : 0 < (radius w)^3 := lt_of_lt_of_le (by norm_num) hc
  have hcoef : 2/(radius w)^3 ≤ 4 := (div_le_iff₀ hp).mpr (by nlinarith)
  have hg := Gravity.gradient3_bound 1 (by norm_num) (position w) x
  simp only [mul_one,position_norm] at hg
  exact hg.trans (mul_le_mul_of_nonneg_right hcoef (enorm_nonneg x))

/-- Every-time response gains for an arbitrary continuous bounded forcing.
The Euclidean norm is transported through mathlib's continuous equivalence,
so a coordinatewise supremum norm is not substituted for physical magnitude. -/
theorem gravity_response_bound (w : ℝ → Fin 4 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (r : ℝ → Vec3) {R : ℝ} (hR : 0 ≤ R)
    (hF : Continuous F) (hH : Continuous H) (hr : Continuous r)
    (hrad : ∀ t ∈ Icc (0:ℝ) (3/5), 7997/10000 ≤ radius (w t))
    (hdF : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (lift (w t))*F t) t)
    (hdH : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (lift (w t))*H t) t)
    (hiF : F 0 = 1) (hiH : H 0 = 1)
    (hb : ∀ t ∈ Icc (0:ℝ) (3/5), GNC.enorm (r t) ≤ R) :
    ∀ t ∈ Icc (0:ℝ) (3/5),
      GNC.enorm (remainder F H r t 0) ≤ (9/14)*R ∧
      GNC.enorm (remainder F H r t 1) ≤ (15/7)*R := by
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) (3/5)) :=
    remainder_derivatives w F H r hF hH hr hdF hdH hiF hiH ht
  apply SecondOrderBound.horizon_three_fifths
    (fun t => euclideanEquiv (remainder F H r t 0))
    (fun t => euclideanEquiv (remainder F H r t 1))
    (fun t => euclideanEquiv (Gravity.gradient3 1 (position (w t)) (remainder F H r t 0)+r t)) hR
  · exact (euclideanEquiv.continuous.comp (remainder_continuous F H r hF hH hr 0)).continuousOn
  · exact (euclideanEquiv.continuous.comp (remainder_continuous F H r hF hH hr 1)).continuousOn
  · intro t ht
    exact (euclideanEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hd t (Ico_subset_Icc_self ht)).1).hasDerivWithinAt
  · intro t ht
    exact (euclideanEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hd t (Ico_subset_Icc_self ht)).2).hasDerivWithinAt
  · rw [remainder_initial]; exact map_zero euclideanEquiv
  · rw [remainder_initial]; exact map_zero euclideanEquiv
  · intro t ht
    exact (enorm_add_le _ _).trans (add_le_add
      (gradient_four (w t) _ (hrad t (Ico_subset_Icc_self ht))) (hb t (Ico_subset_Icc_self ht)))

end GNC.Applications.OrbitalFuel.RetainedPhysical
