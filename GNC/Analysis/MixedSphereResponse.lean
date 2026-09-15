import GNC.Analysis.ReducedSphereResponse

/-! Retain the two mixed axial/transverse responses. The only omitted
quadratic source is then proportional to the square of the cap depth.
Time-polynomial approximations of these curves require separate defect
bounds, as supplied by the physical coefficient certificates. -/
noncomputable section
namespace GNC.MixedSphereResponse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def value (u v c : ℝ) (U V D Q W Cu Cv : E) : E :=
  ReducedSphereResponse.value u v c U V D Q W + (c*u) • Cu + (c*v) • Cv

theorem derivative
    (A : ℝ → E →ₗ[ℝ] E) (H : ℝ → E →ₗ[ℝ] E →ₗ[ℝ] E)
    (U V C D Q W Cu Cv fU fV fC : ℝ → E) (u v c t : ℝ)
    (hs : u^2+v^2=2*c-c^2)
    (hU : HasDerivAt U (A t (U t)+fU t) t)
    (hV : HasDerivAt V (A t (V t)+fV t) t)
    (hD : HasDerivAt D (A t (D t)+fC t+2 • H t (V t) (V t)) t)
    (hQ : HasDerivAt Q (A t (Q t)+H t (U t) (U t)-H t (V t) (V t)) t)
    (hW : HasDerivAt W (A t (W t)+H t (U t) (V t)+H t (V t) (U t)) t)
    (hCu : HasDerivAt Cu (A t (Cu t)+H t (C t) (U t)+H t (U t) (C t)) t)
    (hCv : HasDerivAt Cv (A t (Cv t)+H t (C t) (V t)+H t (V t) (C t)) t) :
    HasDerivAt (fun s => value u v c (U s) (V s) (D s) (Q s) (W s) (Cu s) (Cv s))
      (A t (value u v c (U t) (V t) (D t) (Q t) (W t) (Cu t) (Cv t)) +
        ReducedSphereResponse.first u v c (fU t) (fV t) (fC t) +
        H t (ReducedSphereResponse.first u v c (U t) (V t) (C t))
          (ReducedSphereResponse.first u v c (U t) (V t) (C t)) -
        c^2 • (H t (C t) (C t)-H t (V t) (V t))) t := by
  have h := ((ReducedSphereResponse.derivative_with_defect A H U V C D Q W
    fU fV fC u v c t hs hU hV hD hQ hW).add (hCu.const_smul (c*u))).add
    (hCv.const_smul (c*v))
  convert h using 1
  unfold value ReducedSphereResponse.omitted
  simp only [map_add,map_smul]
  module

theorem omitted_bound (H : E →ₗ[ℝ] E →ₗ[ℝ] E) (C V : E)
    {c σ : ℝ} (hc : |c|≤σ^2) :
    ‖c^2 • (H C C-H V V)‖≤σ^4*‖H C C-H V V‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_pow]
  have h : |c|^2≤σ^4 := by nlinarith [abs_nonneg c,sq_nonneg σ]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

end GNC.MixedSphereResponse
