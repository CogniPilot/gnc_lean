import GNC.Analysis.MatrixODE
import GNC.Applications.OrbitalFuel.ReferenceExistence
import GNC.Applications.OrbitalFuel.ValidatedSolarComparator

/-! An existing physical solar reference and its gravity transition blocks.
The resulting fuel-program certificate has no trajectory-existence premise.
Actual switched chaser existence and attitude realization are separate tasks.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ReferenceFlowExistence
open GNC GNC.PolynomialOrbit GNC.PolynomialOrbitTransition
open GNC.SharedBias GNC.FuelCertificate
open SharedBiasExample (axis)
open SharedBiasCertificates.Solar (kappa x)
open scoped Matrix.Norms.Elementwise

/-- The physical reference equations and initialized gravity variational
equations on the complete mission interval. The global positive-radius
representative is only required to obey the physical ODE on that interval. -/
structure Flow where
  w : ℝ → Fin 4 → ℝ
  F : ℝ → Matrix (Fin 4) (Fin 4) ℝ
  H : ℝ → Matrix (Fin 2) (Fin 2) ℝ
  hw : Continuous w
  hF : Continuous F
  hH : Continuous H
  hr : ∀ t, 0 < radius (w t)
  hdw : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
    HasDerivAt w (physicalRate (PolynomialTransition.alpha:ℝ) (w t)) t
  hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
    HasDerivAt F (planeGenerator (lift (w t))*F t) t
  hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
    HasDerivAt H (normalGenerator (lift (w t))*H t) t
  hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)]
  hiF : F 0 = 1
  hiH : H 0 = 1

theorem plane_continuous (z : ℝ → Fin 5 → ℝ) (hz : Continuous z) :
    Continuous (fun t => planeGenerator (z t)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact continuous_const
    | change Continuous (fun t => 3*z t 4^5*z t 0^2-z t 4^3); fun_prop
    | change Continuous (fun t => 3*z t 4^5*z t 0*z t 1); fun_prop
    | change Continuous (fun t => 3*z t 4^5*z t 1^2-z t 4^3); fun_prop

theorem normal_continuous (z : ℝ → Fin 5 → ℝ) (hz : Continuous z) :
    Continuous (fun t => normalGenerator (z t)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact continuous_const
    | change Continuous (fun t => -z t 4^3); fun_prop

/-- The exact nonlinear reference and both exact transition matrices exist;
neither a supplied trajectory nor a supplied matrix solution is assumed. -/
theorem exists_reference_flow : Nonempty Flow := by
  obtain ⟨w,hw,hr,hiw,hdw⟩ := ReferenceExistence.exists_physical_reference
  have hz := lift_continuous hw hr
  obtain ⟨F,hF,hiF,hdF⟩ := MatrixODE.exists_fundamental _ (plane_continuous _ hz)
  obtain ⟨H,hH,hiH,hdH⟩ := MatrixODE.exists_fundamental _ (normal_continuous _ hz)
  exact ⟨⟨w,F,H,hw,hF,hH,hr,hdw,fun t _ => hdF t,fun t _ => hdH t,hiw,hiF,hiH⟩⟩

def coefficients (r : Flow) := BurnSensitivity.physicalH (fun t => lift (r.w t)) r.F r.H
def budgets (r : Flow) := ValidatedSolarFuel.physicalB (fun t => lift (r.w t)) r.F r.H

/-- Feasibility for the shared-bias candidate and the explicit independent
comparator, and a universal quantitative cost bound over that comparison
program. This proposition concerns the declared terminal program. -/
def CertifiedProgram (r : Flow) : Prop :=
  CommonFeasible axis kappa (coefficients r) (budgets r) x ∧
  IndependentFeasible axis kappa (coefficients r) (budgets r) SolarComparator.plan ∧
  (∀ j, 0 ≤ SolarComparator.plan j ∧ SolarComparator.plan j ≤ 1) ∧
  ∀ y : Fin 18 → ℝ,
    IndependentFeasible axis kappa (coefficients r) (budgets r) y →
    (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
    (Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) x <
      (9891/10000:ℝ)*Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y) ∧
    Propellant.consumedMass 500 (588399/20)
        (Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) x) <
      (99/100:ℝ)*Propellant.consumedMass 500 (588399/20)
        (Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y)

theorem reference_program_certified (r : Flow) : CertifiedProgram r := by
  have hc := ValidatedSolarFuel.physical_reference_certificate r.w r.F r.H
    r.hw r.hF r.hH r.hr r.hdw r.hdF r.hdH r.hiw r.hiF r.hiH
  have hy := ValidatedSolarComparator.physical_reference_feasible r.w r.F r.H
    r.hw r.hF r.hH r.hr r.hdw r.hdF r.hdH r.hiw r.hiF r.hiH
  exact ⟨hc.1,hy,SolarComparator.in_box,hc.2⟩

/-- A nonempty, exact reference-dependent fuel comparison exists. The
reference, its noncollision and its variational flows are conclusions. -/
theorem exists_certified_reference : ∃ r : Flow, CertifiedProgram r := by
  obtain ⟨r⟩ := exists_reference_flow
  exact ⟨r,reference_program_certified r⟩

end GNC.Applications.OrbitalFuel.ReferenceFlowExistence
