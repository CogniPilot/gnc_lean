import GNC.Control.ReferenceTube

/-! Actual derivatives and first-exit certificates for time-varying metrics.
P may follow the reference and its transition; its derivative is mandatory.
No state-dependent metric or geodesic claim is made here.
-/
noncomputable section
open Set Real
namespace GNC.MovingMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem storage_derivative {P : ℝ → E →L[ℝ] E} {dP : E →L[ℝ] E}
    {e : ℝ → E} {de : E} {t : ℝ}
    (hP : HasDerivAt P dP t) (he : HasDerivAt e de t)
    (hsymm : ∀ u v, inner ℝ u (P t v) = inner ℝ v (P t u)) :
    HasDerivAt (fun s => PolytopicTube.storage (P s) (e s))
      (2*inner ℝ (e t) (P t de)+inner ℝ (e t) (dP (e t))) t := by
  convert he.inner ℝ (hP.clm_apply he) using 1
  simp only [inner_add_right, hsymm de (e t)]
  ring

/-- The material derivative of a reference-dependent quadratic storage
closes a moving tube by a boundary inequality on the actual trajectory. -/
theorem boundary_invariance (P dP : ℝ → E →L[ℝ] E)
    (hP : ∀ s, HasDerivAt P (dP s) s)
    (hsymm : ∀ s u v, inner ℝ u (P s v) = inner ℝ v (P s u))
    {e de : ℝ → E} {ρ dρ : ℝ → ℝ} {a b : ℝ}
    (he : ∀ s ∈ Icc a b, HasDerivAt e (de s) s)
    (hρ : ∀ s, HasDerivAt ρ (dρ s) s)
    (hinit : PolytopicTube.storage (P a) (e a) ≤ ρ a)
    (hinward : ∀ s ∈ Ico a b,
      PolytopicTube.storage (P s) (e s) = ρ s →
      2*inner ℝ (e s) (P s (de s))+inner ℝ (e s) (dP s (e s)) < dρ s) :
    ∀ t ∈ Icc a b, PolytopicTube.storage (P t) (e t) ≤ ρ t := by
  have hder := fun s hs => storage_derivative (hP s) (he s hs) (hsymm s)
  exact fun t ht => image_le_of_deriv_right_lt_deriv_boundary
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hder s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt)
    hinit hρ hinward ht

/-- A scheduled generator plus a convex uncertainty set inherits a moving
metric certificate. The scheduled part is never replaced by arbitrary
switching between its values at different reference times. -/
theorem scheduled_vertex_supply {ι W : Type*} [Fintype ι]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (P dP A₀ : E →L[ℝ] E) (A : ι → E →L[ℝ] E)
    (B : W →L[ℝ] E) (weights : ι → ℝ) (α μ : ℝ)
    (hw : ∀ i, 0 ≤ weights i) (hs : ∑ i, weights i = 1)
    (hvertex : ∀ i x w,
      2*inner ℝ x (P (A₀ x+A i x+B w))+inner ℝ x (dP x)+
        α*PolytopicTube.storage P x ≤ μ*‖w‖^2)
    (x : E) (w : W) :
    2*inner ℝ x (P (A₀ x+(∑ i, weights i • A i x)+B w))+
      inner ℝ x (dP x)+α*PolytopicTube.storage P x ≤ μ*‖w‖^2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hvertex i x w) (hw i))
  simp only [map_add, inner_add_right, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, hs, one_mul] at h
  simpa only [map_add, map_sum, map_smul, inner_add_right, inner_sum,
    inner_smul_right, mul_add, Finset.mul_sum, mul_assoc, mul_left_comm] using h

/-- Controller-independent mission certificate, including P-dot and an
explicit nonlinear/model residual. The universal regional inequality is
checked on the whole proposed tube; the conclusion does not assume the
actual trajectory stays there. E can include log pose, rate, servo, filter,
estimator and PID integrator errors together. -/
theorem certified_reference_tube {W : Type*}
    (P dP : ℝ → E →L[ℝ] E)
    (hP : ∀ s, HasDerivAt P (dP s) s)
    (hsymm : ∀ s u v, inner ℝ u (P s v) = inner ℝ v (P s u))
    (f : ℝ → E → W → E) (disturbances : ℝ → Set W)
    (region safe : ℝ → Set E)
    {x reference : ℝ → E} {w : ℝ → W} {dr : ℝ → E}
    {ρ dρ α β reserve : ℝ → ℝ} {a b : ℝ}
    (hx : ∀ s ∈ Icc a b, HasDerivAt x (f s (x s) (w s)) s)
    (hr : ∀ s ∈ Icc a b, HasDerivAt reference (dr s) s)
    (hρ : ∀ s, HasDerivAt ρ (dρ s) s)
    (hw : ∀ s ∈ Ico a b, w s ∈ disturbances s)
    (hinit : PolytopicTube.storage (P a) (x a-reference a) ≤ ρ a)
    (hregion : ∀ s ∈ Icc a b, ∀ y,
      PolytopicTube.storage (P s) (y-reference s) ≤ ρ s → y ∈ region s)
    (hsafe : ∀ s ∈ Icc a b, ∀ y,
      PolytopicTube.storage (P s) (y-reference s) ≤ ρ s → y ∈ safe s)
    (hsupply : ∀ s ∈ Ico a b, ∀ y ∈ region s, ∀ d ∈ disturbances s,
      2*inner ℝ (y-reference s) (P s (f s y d-dr s))+
        inner ℝ (y-reference s) (dP s (y-reference s))+
        α s*PolytopicTube.storage (P s) (y-reference s) ≤ β s)
    (hreserve : ∀ s ∈ Ico a b, 0 < reserve s)
    (hradius : ∀ s ∈ Ico a b, β s+reserve s ≤ dρ s+α s*ρ s) :
    ∀ t ∈ Icc a b,
      PolytopicTube.storage (P t) (x t-reference t) ≤ ρ t ∧
      x t ∈ region t ∩ safe t := by
  have htube := boundary_invariance P dP hP hsymm
    (fun s hs => (hx s hs).sub (hr s hs)) hρ hinit (by
      intro s hs he
      change PolytopicTube.storage (P s) (x s-reference s) = ρ s at he
      have h := hsupply s hs (x s) (hregion s ⟨hs.1,hs.2.le⟩ (x s) he.le)
        (w s) (hw s hs)
      rw [he] at h
      have h₁ := hradius s hs
      have h₂ := hreserve s hs
      simp only [Pi.sub_apply]
      linarith)
  intro t ht
  exact ⟨htube t ht,hregion t ht (x t) (htube t ht),hsafe t ht (x t) (htube t ht)⟩

end GNC.MovingMetric
