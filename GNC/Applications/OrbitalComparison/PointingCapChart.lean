import GNC.Applications.OrbitalComparison.PointingCapBurn

/-! The forward pointing cap in the paper's two independent transverse
coordinates is exactly the algebraic domain used by the physical checker. -/
noncomputable section
namespace GNC.OrbitalComparison.PointingCapChart
open PointingCapBurn

def input (u v : ℝ) : Fin 3 → ℝ := ![u,v,1-Real.sqrt (1-u^2-v^2)]

theorem admissible {σ u v : ℝ} (hσ : σ^2≤1) (h : u^2+v^2≤σ^2) :
    Admissible σ (input u v) := by
  have hr := Real.sq_sqrt (show 0≤1-u^2-v^2 by nlinarith)
  have hn := Real.sqrt_nonneg (1-u^2-v^2)
  have hu := sq_nonneg u
  have hv := sq_nonneg v
  change 0≤1-Real.sqrt (1-u^2-v^2) ∧ 1-Real.sqrt (1-u^2-v^2)≤1 ∧
    u^2+v^2=2*(1-Real.sqrt (1-u^2-v^2))-(1-Real.sqrt (1-u^2-v^2))^2 ∧
    u^2+v^2≤σ^2
  exact ⟨by nlinarith,by linarith,by nlinarith,h⟩

theorem input_eq {σ : ℝ} {x : Fin 3 → ℝ} (h : Admissible σ x) :
    x=input (x 0) (x 1) := by
  have hs : 1-x 0^2-x 1^2=(1-x 2)^2 := by nlinarith [h.2.2.1]
  have hr : Real.sqrt (1-x 0^2-x 1^2)=1-x 2 := by
    rw [hs,Real.sqrt_sq (sub_nonneg.mpr h.2.1)]
  ext i
  fin_cases i <;> simp [input,hr]

theorem admissible_iff {σ : ℝ} (hσ : σ^2≤1) (x : Fin 3 → ℝ) :
    Admissible σ x ↔ x 0^2+x 1^2≤σ^2 ∧ x=input (x 0) (x 1) := by
  constructor
  · intro h
    exact ⟨h.2.2.2,input_eq h⟩
  · rintro ⟨h,he⟩
    exact he.symm ▸ admissible hσ h

end GNC.OrbitalComparison.PointingCapChart
