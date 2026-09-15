import GNC.Applications.OrbitalComparison.SpatialTerminalCertificate
import GNC.Applications.OrbitalComparison.SpatialData.RTNFrameCircleTime14
import GNC.Applications.OrbitalComparison.SpatialData.RTNInertialCircleTime14
import GNC.Applications.OrbitalComparison.SpatialData.InertialCircleTime14
import GNC.Analysis.EuclideanBox

/-! Kernel-checked physical burn-end boxes for all three 600-second laws.
The bounds include stored-coefficient prediction error and the error of the
computed physical nominal. Integer metres and hundredths of metres/second
are outward display roundings, not numerical ODE error allowances. -/
namespace GNC.OrbitalComparison.SpatialTerminalBounds
open SpatialBurn SpatialFieldCertificate SpatialTerminalCertificate Set

def record : Law → Data (C := CirclePolynomial.Coefficients)
  | .rtnReferenceOffset => SpatialData.RTNFrameCircleTime14.data
  | .rtnInertialOffset => SpatialData.RTNInertialCircleTime14.data
  | .inertiallyFixed => SpatialData.InertialCircleTime14.data

theorem record_valid (mode : Law) :
    (record mode).Valid SpatialSources.circle WeightedCertificate.circleTime mode := by
  cases mode
  · exact SpatialData.RTNFrameCircleTime14.valid
  · exact SpatialData.RTNInertialCircleTime14.valid
  · exact SpatialData.InertialCircleTime14.valid

def positionBox : Law → Fin 3 → ℚ
  | .rtnReferenceOffset => ![312,764,555]
  | .rtnInertialOffset => ![312,751,552]
  | .inertiallyFixed => ![205,759,555]

def velocityBox : Law → Fin 3 → ℚ
  | .rtnReferenceOffset => ![121/100,252/100,179/100]
  | .rtnInertialOffset => ![121/100,245/100,174/100]
  | .inertiallyFixed => ![83/100,255/100,179/100]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem numbers (mode : Law) (i : Fin 3) :
    positionRadius (record mode) 1 (7/20) i ≤ positionBox mode i ∧
    velocityRadius (record mode) 1 (7/20) i ≤ velocityBox mode i := by
  cases mode <;> fin_cases i <;> decide +kernel

/-- Simultaneous six-dimensional enclosure for every admissible physical
trajectory at the 600-second epoch, with inertial coordinate components. -/
theorem endpoint_box (mode : Law) {θ : ℝ}
    (X : PhysicalOrbit mode θ) (X₀ : PhysicalOrbit mode 0) (hθ : |θ| ≤ 7/20) :
    ∀ i : Fin 3,
      |(X.p 1-X₀.p 1) i| ≤ (positionBox mode i:ℝ) ∧
      |(X.v 1-X₀.v 1) i|/600 ≤ (velocityBox mode i:ℝ) := by
  intro i
  have h := relative_bounds (record mode) mode (record_valid mode) X X₀ 1 (7/20)
    (by norm_num) (by norm_num [UniformCertificate.angle]) (by norm_num; exact hθ) i
  norm_num only [Rat.cast_one] at h
  exact ⟨h.1.trans (Rat.cast_le.mpr (numbers mode i).1),
    h.2.trans (Rat.cast_le.mpr (numbers mode i).2)⟩

theorem squared_budgets (mode : Law) :
    (∑ i, (positionBox mode i)^2) ≤ (1000:ℚ)^2 ∧
    (∑ i, (velocityBox mode i)^2) ≤ (7/2:ℚ)^2 := by
  cases mode <;> decide +kernel

/-- An illustrative burn-end screening requirement, in SI units. These
limits are specifications on actual deviation, not ODE error allowances. -/
theorem endpoint_screen (mode : Law) {θ : ℝ}
    (X : PhysicalOrbit mode θ) (X₀ : PhysicalOrbit mode 0) (hθ : |θ| ≤ 7/20) :
    ‖X.p 1-X₀.p 1‖ ≤ 1000 ∧ ‖X.v 1-X₀.v 1‖/600 ≤ 7/2 := by
  have h := endpoint_box mode X X₀ hθ
  constructor
  · change enorm (fun i => (X.p 1-X₀.p 1) i) ≤ 1000
    apply enorm_le_of_component_bounds _ (fun i => (positionBox mode i:ℝ))
      (fun i => (h i).1) (by norm_num)
    exact_mod_cast (squared_budgets mode).1
  · have hv : enorm ((1/600:ℝ) • (fun i => (X.v 1-X₀.v 1) i)) ≤ 7/2 := by
      refine enorm_le_of_component_bounds _ (fun i => (velocityBox mode i:ℝ))
        ?_ (by norm_num) ?_
      · intro i
        simpa [abs_mul,div_eq_mul_inv,mul_comm] using (h i).2
      · have hq : ((∑ i, (velocityBox mode i)^2:ℚ):ℝ) ≤ (((7/2:ℚ)^2:ℚ):ℝ) :=
          Rat.cast_le.mpr (squared_budgets mode).2
        push_cast at hq
        exact hq
    rw [enorm_smul] at hv
    change |(1/600:ℝ)| * ‖X.v 1-X₀.v 1‖ ≤ 7/2 at hv
    simpa [div_eq_mul_inv,mul_comm] using hv

end GNC.OrbitalComparison.SpatialTerminalBounds
