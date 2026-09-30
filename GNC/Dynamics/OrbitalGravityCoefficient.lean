import GNC.Dynamics.OrbitalPolytopicTube
import GNC.Analysis.VanishingCoefficient

/-! Exact A0 + Delta A representation for the actual orbital log-gravity
residual. The coefficient tends to zero at zero tracking error, with an
explicit origin-relative bound. The witness need not be evaluated online.
No controller or actuator realization is inferred from this theorem.
-/
noncomputable section
namespace GNC.OrbitalGravityCoefficient
open OrbitalNearAffine OrbitalLogTube
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem representation (A₀ : E →L[ℝ] E)
    (encode : E → LogState) (inject : Vec3 → E)
    (μ : ℝ) (hμ : 0 ≤ μ) (frame : SO3) (q : Vec3)
    {r D p α w R : ℝ} (hp : 0 ≤ p) (hα : 0 ≤ α) (hw : 0 ≤ w)
    (hR : 0 ≤ R) (hD : D < r) (hq : r ≤ enorm q)
    (hpos : ∀ z, enorm (encode z 0) ≤ p*‖z‖)
    (hang : ∀ z, enorm (encode z 2) ≤ α*‖z‖)
    (hout : ∀ v, ‖inject v‖ ≤ w*enorm v)
    (hpd : p*R ≤ D) (had : α*R ≤ 1) :
    ∃ Δ : E → E →L[ℝ] E, Δ 0 = 0 ∧
      ∀ z, ‖z‖ ≤ R →
        (A₀ + Δ z) z = A₀ z + inject (residual μ frame q (encode z)) ∧
        ‖Δ z‖ ≤ coefficient μ r D p α w q * ‖z‖ := by
  exact VanishingCoefficient.representation A₀ _ hR
    (OrbitalPolytopicTube.gravity_quadratic encode inject μ hμ frame q
      hp hα hw hD hq hpos hang hout hpd had)

end GNC.OrbitalGravityCoefficient
