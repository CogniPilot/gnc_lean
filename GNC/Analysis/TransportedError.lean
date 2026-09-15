import GNC.Analysis.ForcedResponse
import GNC.Control.ReferenceTube

/-! Reference-dependent transport of nonlinear error tubes.

The known time-varying generator A is retained exactly in the change of
coordinates. An approximate transition has its own generator defect D.
Only the transported nonlinear residual and D enter the transformed dynamics;
the size of A itself need not inflate the residual bound.
-/
noncomputable section
open Set Real
namespace GNC.TransportedError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
abbrev End := E →L[ℝ] E

def coordinates (Φ : ℝ → (End (E := E))ˣ) (e : ℝ → E) (t : ℝ) : E :=
  ((Φ t)⁻¹).val (e t)

/-- Exact pullback by an approximate invertible transition. D is the
generator defect, i.e. Phi'=(A+D)Phi, not an assumed bound on A. -/
theorem coordinates_derivative (Φ : ℝ → (End (E := E))ˣ)
    (A D : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) ((A t+D t)*(Φ t).val) t)
    {e : ℝ → E} {r : E} {t : ℝ}
    (he : HasDerivAt e (A t (e t)+r) t) :
    HasDerivAt (coordinates Φ e)
      (((Φ t)⁻¹).val (r-D t (e t))) t := by
  have h := (ForcedResponse.inverse_derivative Φ (fun s => A s+D s) hΦ t).clm_apply he
  convert h using 1
  simp [ContinuousLinearMap.mul_apply, map_add, map_sub]
  module

theorem reconstruct (Φ : ℝ → (End (E := E))ˣ) (e : ℝ → E) (t : ℝ) :
    (Φ t).val (coordinates Φ e t) = e t :=
  ForcedResponse.cancel (Φ t) (e t)

/-- The generator part cancels from the actual derivative of the
transported quadratic energy. This includes the Magnus defect term. -/
theorem transported_storage_derivative (P : End (E := E))
    (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    (Φ : ℝ → (End (E := E))ˣ) (A D : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) ((A t+D t)*(Φ t).val) t)
    {e : ℝ → E} {r : E} {t : ℝ}
    (he : HasDerivAt e (A t (e t)+r) t) :
    HasDerivAt (fun s => PolytopicTube.storage P (coordinates Φ e s))
      (2*inner ℝ (coordinates Φ e t) (P (((Φ t)⁻¹).val (r-D t (e t))))) t :=
  PolytopicTube.storage_derivative P hP (coordinates_derivative Φ A D hΦ he)

/-- Propagating an ellipsoid by Phi gives the corresponding tube in the
original error coordinates. This preserves the full linear shape. -/
theorem transported_sublevel_iff (P : End (E := E))
    (Φ : (End (E := E))ˣ) (e : E) (ρ : ℝ) :
    PolytopicTube.storage P ((Φ⁻¹).val e) ≤ ρ ↔
      e ∈ Φ.val '' Reachability.sublevel (PolytopicTube.storage P) ρ := by
  constructor
  · intro h
    exact ⟨(Φ⁻¹).val e,h,ForcedResponse.cancel Φ e⟩
  · rintro ⟨z,hz,rfl⟩
    simpa only [ForcedResponse.cancel'] using hz

/-- A norm bound on the transported defect contributes at most twice
that bound to squared-error growth. Large skew transport is not charged. -/
theorem defect_energy_bound (F : End (E := E)) {ε : ℝ}
    (hF : ‖F‖ ≤ ε) (z : E) :
    2*inner ℝ z (-F z) ≤ 2*ε*‖z‖^2 := by
  have hf := (F.le_opNorm z).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg z))
  have h := real_inner_le_norm z (-F z)
  rw [norm_neg] at h
  have hh := mul_le_mul_of_nonneg_left hf (norm_nonneg z)
  nlinarith

/-- An anisotropic tube propagated by an approximate transition. The
regional supply is checked for every pulled-back state in the sublevel
set. Its first-exit proof accounts for both the nonlinear residual and
the generator defect, and never replaces the known A by its norm. -/
theorem certified_tube {W : Type*}
    (P : End (E := E))
    (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    (Φ : ℝ → (End (E := E))ˣ) (A D : ℝ → End (E := E))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) ((A t+D t)*(Φ t).val) t)
    (r : ℝ → E → W → E) (disturbances : ℝ → Set W)
    {e : ℝ → E} {w : ℝ → W}
    {ρ dρ α β reserve : ℝ → ℝ} {a b : ℝ}
    (he : ∀ t ∈ Icc a b, HasDerivAt e (A t (e t)+r t (e t) (w t)) t)
    (hw : ∀ t ∈ Ico a b, w t ∈ disturbances t)
    (hρ : ∀ t, HasDerivAt ρ (dρ t) t)
    (hinit : PolytopicTube.storage P (coordinates Φ e a) ≤ ρ a)
    (hsupply : ∀ t ∈ Ico a b, ∀ z,
      PolytopicTube.storage P z ≤ ρ t → ∀ d ∈ disturbances t,
      2*inner ℝ z (P (((Φ t)⁻¹).val
        (r t ((Φ t).val z) d-D t ((Φ t).val z))))+
        α t*PolytopicTube.storage P z ≤ β t)
    (hreserve : ∀ t ∈ Ico a b, 0 < reserve t)
    (hradius : ∀ t ∈ Ico a b, β t+reserve t ≤ dρ t+α t*ρ t) :
    ∀ t ∈ Icc a b,
      e t ∈ (Φ t).val '' Reachability.sublevel (PolytopicTube.storage P) (ρ t) := by
  have hder := fun t ht => transported_storage_derivative P hP Φ A D hΦ (he t ht)
  have hbound : ∀ t ∈ Icc a b, PolytopicTube.storage P (coordinates Φ e t) ≤ ρ t := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt) hinit hρ
    intro t ht hb
    have h := hsupply t ht (coordinates Φ e t) hb.le (w t) (hw t ht)
    rw [reconstruct, hb] at h
    have h₁ := hradius t ht
    have h₂ := hreserve t ht
    linarith
  intro t ht
  exact (transported_sublevel_iff P (Φ t) (e t) (ρ t)).mp (hbound t ht)

end GNC.TransportedError
