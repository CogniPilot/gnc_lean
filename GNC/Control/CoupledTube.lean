import GNC.Control.ReferenceTube

/-! Joint outer/inner-loop certificates without a constant inner-error
replacement. The scalar energies may themselves be scheduled quadratic
storages of multidimensional states. Both coupling directions are retained.
-/
noncomputable section
open Set Real
namespace GNC.CoupledTube

/-- A weighted joint energy absorbs two-way coupling whenever the
displayed small-gain margins hold. Backstepping can improve these margins
by cancelling cross power before applying this inequality. -/
theorem supply {Vo Vi dVo dVi ao ai bo bi weight rate do_ di_ : ℝ}
    (ho : 0 ≤ Vo) (hi : 0 ≤ Vi) (hweight : 0 ≤ weight)
    (houter : dVo ≤ -ao*Vo+bo*Vi+do_)
    (hinner : dVi ≤ bi*Vo-ai*Vi+di_)
    (hm₁ : rate ≤ ao-weight*bi) (hm₂ : rate*weight ≤ weight*ai-bo) :
    dVo+weight*dVi+rate*(Vo+weight*Vi) ≤ do_+weight*di_ := by
  have h := mul_le_mul_of_nonneg_left hinner hweight
  have h₁ := mul_le_mul_of_nonneg_right hm₁ ho
  have h₂ := mul_le_mul_of_nonneg_right hm₂ hi
  nlinarith

/-- Coupled regional differential bounds close one joint tube. Rate error
is an evolving state, so feedback from the outer error is not discarded. -/
theorem invariant_tube {Vo Vi dVo dVi : ℝ → ℝ}
    {ao ai bo bi rate do_ di_ ρ dρ reserve : ℝ → ℝ} {weight a b : ℝ}
    (hweight : 0 ≤ weight)
    (ho : ∀ s ∈ Icc a b, HasDerivAt Vo (dVo s) s)
    (hi : ∀ s ∈ Icc a b, HasDerivAt Vi (dVi s) s)
    (hVo : ∀ s ∈ Icc a b, 0 ≤ Vo s)
    (hVi : ∀ s ∈ Icc a b, 0 ≤ Vi s)
    (hρ : ∀ s, HasDerivAt ρ (dρ s) s)
    (hinit : Vo a+weight*Vi a ≤ ρ a)
    (hsupply : ∀ s ∈ Ico a b, Vo s+weight*Vi s ≤ ρ s →
      dVo s ≤ -ao s*Vo s+bo s*Vi s+do_ s ∧
      dVi s ≤ bi s*Vo s-ai s*Vi s+di_ s)
    (hm₁ : ∀ s ∈ Ico a b, rate s ≤ ao s-weight*bi s)
    (hm₂ : ∀ s ∈ Ico a b, rate s*weight ≤ weight*ai s-bo s)
    (hreserve : ∀ s ∈ Ico a b, 0 < reserve s)
    (hradius : ∀ s ∈ Ico a b,
      do_ s+weight*di_ s+reserve s ≤ dρ s+rate s*ρ s) :
    ∀ t ∈ Icc a b, Vo t+weight*Vi t ≤ ρ t := by
  have hder := fun s hs => (ho s hs).add ((hi s hs).const_mul weight)
  apply image_le_of_deriv_right_lt_deriv_boundary
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hder s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt) hinit hρ
  intro s hs he
  change Vo s+weight*Vi s = ρ s at he
  have hc := hsupply s hs he.le
  have h := supply (hVo s ⟨hs.1,hs.2.le⟩) (hVi s ⟨hs.1,hs.2.le⟩)
    hweight hc.1 hc.2 (hm₁ s hs) (hm₂ s hs)
  rw [he] at h
  have h₁ := hradius s hs
  have h₂ := hreserve s hs
  linarith

end GNC.CoupledTube
