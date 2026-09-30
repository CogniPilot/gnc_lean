import GNC.Control.PolytopicResidualTube
import GNC.Dynamics.OrbitalLogTube

/-! The actual orbital log-gravity residual supplies the nonlinear sector
needed by the polytopic BIBO theorem. Coordinates and acceleration injection
have explicit norm gains, avoiding an implicit identification of the sup
norm on `LogState` with a Euclidean quadratic-storage norm. This establishes
the gravity part of the certificate. An actual closed-loop realization,
vertex enclosure, and disturbance-channel bound remain required. -/
noncomputable section
namespace GNC.OrbitalPolytopicTube
open OrbitalNearAffine OrbitalLogTube PolytopicTube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem gravity_quadratic (encode : E → LogState) (inject : Vec3 → E)
    (μ : ℝ) (hμ : 0 ≤ μ) (frame : SO3) (q : Vec3)
    {r D p α w R : ℝ} (hp : 0 ≤ p) (hα : 0 ≤ α) (hw : 0 ≤ w)
    (hD : D < r) (hq : r ≤ enorm q)
    (hpos : ∀ z, enorm (encode z 0) ≤ p*‖z‖)
    (hang : ∀ z, enorm (encode z 2) ≤ α*‖z‖)
    (hout : ∀ v, ‖inject v‖ ≤ w*enorm v)
    (hpd : p*R ≤ D) (had : α*R ≤ 1) :
    ∀ z, ‖z‖ ≤ R →
      ‖inject (residual μ frame q (encode z))‖ ≤
        coefficient μ r D p α w q * ‖z‖^2 := by
  intro z hz
  have hpd' := (mul_le_mul_of_nonneg_left hz hp).trans hpd
  have had' := (mul_le_mul_of_nonneg_left hz hα).trans had
  have hb := residual_bound μ hμ frame q (encode z) hD hq
    ((hpos z).trans hpd') ((hang z).trans had')
  have hn := enorm_nonneg q
  have hp0 := enorm_nonneg (encode z 0)
  have ha0 := enorm_nonneg (encode z 2)
  have h1 : 2*(μ/enorm q^3)*enorm (encode z 2)*enorm (encode z 0) ≤
      2*(μ/enorm q^3)*(α*‖z‖)*(p*‖z‖) := by
    gcongr <;> first | exact hang z | exact hpos z
  have h2 : (4*μ/(r-D)^4)*enorm (encode z 0)^2 ≤
      (4*μ/(r-D)^4)*(p*‖z‖)^2 := by
    gcongr
    exact hpos z
  exact (hout _).trans ((mul_le_mul_of_nonneg_left
    (hb.trans (add_le_add h1 h2)) hw).trans_eq (by unfold coefficient; ring))

/-- Explicit storage loss from the physical inverse-square gravity model. -/
theorem gravity_supply (P : E →L[ℝ] E)
    (encode : E → LogState) (inject : Vec3 → E)
    (μ : ℝ) (hμ : 0 ≤ μ) (frame : SO3) (q : Vec3)
    {r D p α w R m ρ : ℝ} (hp : 0 ≤ p) (hα : 0 ≤ α) (hw : 0 ≤ w)
    (hD : D < r) (hq : r ≤ enorm q)
    (hpos : ∀ z, enorm (encode z 0) ≤ p*‖z‖)
    (hang : ∀ z, enorm (encode z 2) ≤ α*‖z‖)
    (hout : ∀ v, ‖inject v‖ ≤ w*enorm v)
    (hpd : p*R ≤ D) (had : α*R ≤ 1)
    (hm : 0 < m) (hR : 0 ≤ R)
    (hcoerce : ∀ z, m*‖z‖^2 ≤ storage P z) (hregion : ρ ≤ m*R^2) :
    ∀ z, storage P z ≤ ρ →
      2*inner ℝ z (P (inject (residual μ frame q (encode z)))) ≤
        (2*‖P‖*(coefficient μ r D p α w q*R)/m)*storage P z := by
  exact PolytopicResidualTube.quadratic_supply P _ hm
    (coefficient_nonneg hμ hp hα hw q) hR hcoerce hregion
    (gravity_quadratic encode inject μ hμ frame q hp hα hw hD hq
      hpos hang hout hpd had)

end GNC.OrbitalPolytopicTube
