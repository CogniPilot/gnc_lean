import GNC.Analysis.NearLinearTube
import GNC.Control.LinearQuadraticTube

/-! A nonlinear certificate using an inexact propagator.
Ψ solves its own generator B; it need not solve the physical retained A.
The response of A-B is charged as a linear defect, separately from curvature.
No exact fundamental solution for A is assumed or constructed. -/
noncomputable section
open Set MeasureTheory
namespace GNC.ApproximateLinearTube
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
abbrev End := E →L[ℝ] E

/-- Every differentiable invertible candidate supplies its own generator.
This identity does not assert that it solves the retained physical system. -/
theorem candidate_generator (Ψ : ℝ → (End (E := E))ˣ) (D : ℝ → End (E := E))
    (hD : ∀ t, HasDerivAt (fun s => (Ψ s).val) (D t) t) :
    ∀ t, HasDerivAt (fun s => (Ψ s).val)
      ((D t*((Ψ t)⁻¹).val)*(Ψ t).val) t := by
  intro t
  simpa only [mul_assoc, Units.inv_mul, mul_one] using hD t

/-- A checked differential residual of the candidate supplies the generator
defect after charging the inverse gain. -/
theorem defect_from_residual (U : (End (E := E))ˣ) (A D : End (E := E)) :
    ‖A-D*(U⁻¹).val‖≤‖A*U.val-D‖*‖(U⁻¹).val‖ := by
  have he : A-D*(U⁻¹).val=(A*U.val-D)*(U⁻¹).val := by
    simp only [sub_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [he]
  exact norm_mul_le _ _

theorem weighted_response (K : ℝ → End (E := E)) (r : ℝ → E)
    (e c : ℝ → ℝ) {t R d b : ℝ} (ht : 0≤t) (hR : 0≤R)
    (hK : Continuous K) (hr : Continuous r) (he : Continuous e) (hc : Continuous c)
    (hbnd : ∀ s ∈ Icc 0 t, ‖r s‖≤e s*R+c s*R^2)
    (hegain : (∫ s in 0..t, ‖K s‖*e s)≤d)
    (hcgain : (∫ s in 0..t, ‖K s‖*c s)≤b) :
    ‖∫ s in 0..t, K s (r s)‖≤d*R+b*R^2 := by
  have h1 : Continuous (fun s => ‖K s‖*e s*R) := (hK.norm.mul he).mul_const R
  have h2 : Continuous (fun s => ‖K s‖*c s*R^2) := (hK.norm.mul hc).mul_const (R^2)
  have hm := intervalIntegral.integral_mono_on (μ := volume) ht
    ((hK.clm_apply hr).norm.intervalIntegrable 0 t)
    ((h1.add h2).intervalIntegrable 0 t) (fun s hs => by
      calc
        ‖K s (r s)‖≤‖K s‖*‖r s‖ := (K s).le_opNorm _
        _≤‖K s‖*(e s*R+c s*R^2) := mul_le_mul_of_nonneg_left (hbnd s hs) (norm_nonneg _)
        _=‖K s‖*e s*R+‖K s‖*c s*R^2 := by ring)
  change (∫ s in 0..t, ‖K s (r s)‖)≤
    ∫ s in 0..t, (‖K s‖*e s*R+‖K s‖*c s*R^2) at hm
  rw [intervalIntegral.integral_add (h1.intervalIntegrable 0 t)
    (h2.intervalIntegrable 0 t), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const] at hm
  exact (intervalIntegral.norm_integral_le_integral_norm ht).trans (hm.trans
    (add_le_add (mul_le_mul_of_nonneg_right hegain hR)
      (mul_le_mul_of_nonneg_right hcgain (sq_nonneg R))))

/-- An approximate propagator's generator defect and the nonlinear residual
are both integrated with that propagator's own kernel. Invertibility, the
displayed derivative and the two weighted bounds must be certified. -/
theorem certificate (Ψ : ℝ → (End (E := E))ˣ) (A B : ℝ → End (E := E))
    (hΨ : ∀ t, HasDerivAt (fun s => (Ψ s).val) (B t*(Ψ t).val) t)
    (hΨ₀ : Ψ 0=1) (x r : ℝ → E) (e c : ℝ → ℝ) {T a d b : ℝ}
    (hT : 0≤T) (ha : 0<a) (hd0 : 0≤d) (hd : d<1) (hb : 0≤b)
    (hsmall : 4*a*b<(1-d)^2)
    (hx : Continuous x) (hr : Continuous r) (hA : Continuous A) (hB : Continuous B)
    (he : Continuous e) (hc : Continuous c)
    (hode : ∀ t ∈ Icc 0 T, HasDerivAt x (A t (x t)+r t) t)
    (he0 : ∀ t ∈ Icc 0 T, 0≤e t) (hc0 : ∀ t ∈ Icc 0 T, 0≤c t)
    (hi : ‖x 0‖≤a) (hlin : ∀ t ∈ Icc 0 T, ‖(Ψ t).val (x 0)‖≤a)
    (hdefect : ∀ t ∈ Icc 0 T, ‖A t-B t‖≤e t)
    (hrem : ∀ t ∈ Icc 0 T, ‖x t‖≤2*(a/(1-d)) → ‖r t‖≤c t*‖x t‖^2)
    (hegain : ∀ t ∈ Icc 0 T, (∫ s in 0..t, ‖NearLinearTube.kernel Ψ t s‖*e s)≤d)
    (hcgain : ∀ t ∈ Icc 0 T, (∫ s in 0..t, ‖NearLinearTube.kernel Ψ t s‖*c s)≤b) :
    ∀ t ∈ Icc 0 T,
      ‖x t‖≤LinearQuadraticTube.radius a d b ∧
      ‖x t-(Ψ t).val (x 0)‖≤
        d*LinearQuadraticTube.radius a d b+b*(LinearQuadraticTube.radius a d b)^2 := by
  let r' : ℝ → E := fun t => (A t-B t) (x t)+r t
  have hr' : Continuous r' := ((hA.sub hB).clm_apply hx).add hr
  have hode' (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt x (B t (x t)+r' t) t := by
    convert hode t ht using 1
    simp [r', ContinuousLinearMap.sub_apply]
    abel
  have hid (t : ℝ) (ht : t ∈ Icc 0 T) :=
    NearLinearTube.variation_of_constants Ψ B hΨ hΨ₀ x r' hr' ht.1
      (fun s hs => hode' s ⟨hs.1,hs.2.trans ht.2⟩)
  have hk := NearLinearTube.kernel_continuous Ψ B hΨ
  have hres (R : ℝ) (hR : 0≤R) (hRD : R≤2*(a/(1-d)))
      (s : ℝ) (hs : s ∈ Icc 0 T) (hxR : ‖x s‖≤R) :
      ‖r' s‖≤e s*R+c s*R^2 := by
    have hdR : ‖(A s-B s) (x s)‖≤e s*R :=
      ((A s-B s).le_opNorm _).trans
        (mul_le_mul (hdefect s hs) hxR (norm_nonneg _) (he0 s hs))
    have hcR := (hrem s hs (hxR.trans hRD)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxR 2) (hc0 s hs))
    exact (norm_add_le _ _).trans (add_le_add hdR hcR)
  have total : ∀ t ∈ Icc 0 T, ‖x t‖≤LinearQuadraticTube.radius a d b := by
    apply LinearQuadraticTube.bound hT ha hd0 hd hb hsmall hx.norm hi (fun t _ => norm_nonneg _)
    intro R hR t ht hprefix
    have hw := weighted_response (NearLinearTube.kernel Ψ t) r' e c ht.1 hR.1
      (hk t) hr' he hc (fun s hs => hres R hR.1 hR.2 s ⟨hs.1,hs.2.trans ht.2⟩ (hprefix s hs))
      (hegain t ht) (hcgain t ht)
    rw [hid t ht]
    exact ((norm_add_le _ _).trans (add_le_add (hlin t ht) hw)).trans_eq (by ring)
  have hp := LinearQuadraticTube.properties ha hd hb hsmall
  have hR : 0≤LinearQuadraticTube.radius a d b :=
    (div_nonneg ha.le (sub_pos.mpr hd).le).trans hp.1
  intro t ht
  refine ⟨total t ht, ?_⟩
  rw [hid t ht, add_sub_cancel_left]
  exact weighted_response (NearLinearTube.kernel Ψ t) r' e c ht.1 hR
    (hk t) hr' he hc (fun s hs => hres _ hR hp.2.1.le s
      ⟨hs.1,hs.2.trans ht.2⟩ (total s ⟨hs.1,hs.2.trans ht.2⟩)) (hegain t ht) (hcgain t ht)

end GNC.ApproximateLinearTube
