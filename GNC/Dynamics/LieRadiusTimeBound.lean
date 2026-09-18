import GNC.Dynamics.LieRadiusDefect

/-! Polynomial time budgets for direct full-gravity certification. Quadratic
growth of the inverse-radius offset and scalar-radius errors is retained.
Only the positive radius floor and the smooth inverse-radius multiplier are
bounded uniformly; these depend on the known candidate, not an unknown orbit.
-/
noncomputable section
namespace GNC.LieRadiusTimeBound
open Real Gravity LieRadiusDefect

def forcing (μ r σ δ P H U E B t R C : ℝ) : ℝ :=
  let K := μ/r^3
  let W := (1+σ/2+σ^2/12)*r
  let axisError := (σ/2+σ^2*(2+δ)/12)*δ*r
  let A := (r+P)*(1+H)/r
  R+K*(3*H^2*t^4+H^3*t^6)*(P+W)+3*K*H*axisError*t^2+σ*δ*B+
    K*(3*H*t^2+3*H^2*t^4+H^3*t^6)*(inverseQuadraticBudget σ*r)+
    μ*inverseRadiusFactor A/(r-P)^2*
      (C+E*t^2+(H^2+2*(U+E)*H)*t^4+(U+E)*H^2*t^6)

theorem angle_budget_mono {μ r θ σ δ P H U E C R B : ℝ}
    (hμ : 0≤μ) (hr : 0<r) (hδ : 0≤δ) (hP : 0≤P)
    (hH : 0≤H) (hB : 0≤B) (hθ : |θ|≤σ) :
    budget μ r θ δ P H U E C R B≤budget μ r σ δ P H U E C R B := by
  have hσ := (abs_nonneg θ).trans hθ
  have hs : θ^2≤σ^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg θ) hθ 2
  have hβ := inverseQuadraticBudget_mono (abs_nonneg θ) hθ
  unfold budget
  dsimp only
  rw [abs_of_nonneg hσ]
  gcongr

/-- A rational polynomial can bound the entire pointwise defect. The exact
candidate norm need not be expanded as three Cartesian trajectory jets. -/
theorem budget_le_forcing {μ r σ δ P H U E B t R C : ℝ}
    (hμ : 0≤μ) (hr : 0<r) (hσ : 0≤σ) (hP : 0≤P)
    (hH : 0≤H) (hU : 0≤U) (hE : 0≤E) (hC : 0≤C)
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    budget μ r σ δ P (H*t^2) (U*t^2) (E*t^2) C R B≤
      forcing μ r σ δ P H U E B t R C := by
  have ht2 : t^2≤1 := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have hht : H*t^2≤H := by nlinarith
  have hAt : 0≤(r+P)*(1+H*t^2)/r := by positivity
  have hA : (r+P)*(1+H*t^2)/r≤(r+P)*(1+H)/r := by gcongr
  have hF := inverseRadiusFactor_mono hAt hA
  have hG : μ*inverseRadiusFactor ((r+P)*(1+H*t^2)/r)/(r-P)^2≤
      μ*inverseRadiusFactor ((r+P)*(1+H)/r)/(r-P)^2 := by gcongr
  have hS : 0≤C+E*t^2+(H^2+2*(U+E)*H)*t^4+(U+E)*H^2*t^6 := by positivity
  have he : C+E*t^2+(H*t^2)^2+2*(U*t^2+E*t^2)*(H*t^2)+
      (U*t^2+E*t^2)*(H*t^2)^2=
      C+E*t^2+(H^2+2*(U+E)*H)*t^4+(U+E)*H^2*t^6 := by ring
  unfold budget forcing
  dsimp only
  rw [abs_of_nonneg hσ,he]
  have hm := mul_le_mul_of_nonneg_right hG hS
  convert add_le_add_left hm
    (R+(μ/r^3)*(3*H^2*t^4+H^3*t^6)*(P+(1+σ/2+σ^2/12)*r)+
      3*(μ/r^3)*H*((σ/2+σ^2*(2+δ)/12)*δ*r)*t^2+σ*δ*B+
      (μ/r^3)*(3*H*t^2+3*H^2*t^4+H^3*t^6)*(inverseQuadraticBudget σ*r)) using 1 <;> ring

end GNC.LieRadiusTimeBound
