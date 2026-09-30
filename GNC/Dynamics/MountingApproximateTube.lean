import GNC.Dynamics.MountingOrbitalTube
import GNC.Analysis.ApproximateLinearTube

/-! A body-fixed mounting-error certificate using a computed propagator.
The physical ODE directly supplies the transformed dynamics: a smooth group
logarithm and an exact retained-system STM are not premises. Classical
trajectory existence, candidate invertibility and integral gains remain
explicit. Frame transport, gravity curvature and propagator defects are charged.
-/
noncomputable section
open Set MeasureTheory
namespace GNC.MountingOrbitalError

/-- Continuous-time, non-iterative enclosure for a fixed body mounting error.
The coefficient contains both differential gravity and frame-transport terms.
All quantities are normalized; the norm on LogState is the native box norm. -/
theorem approximate_certificate (μ : ℝ) (hμ : 0≤μ) (φ : Vec3) (hφ : enorm φ≤1)
    (R : ℝ → SO3) (p v q w a ω : ℝ → Vec3) (Φ : ℝ → Endˣ) (B : ℝ → End) (e : ℝ → ℝ)
    {T α δ β r D : ℝ} (hT : 0≤T) (hα : 0<α) (hβ : 0≤β)
    (hδ0 : 0≤δ) (hδ : δ<1) (hsmall : 4*α*β<(1-δ)^2)
    (hD : D<r) (hdom : 4*(α/(1-δ))≤D)
    (hqrad : ∀ t ∈ Icc 0 T, r≤enorm (q t))
    (hR : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (R s).val) ((R t).val*skew (ω t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q (w t) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v
      (Gravity.field3 μ (p t)+rotate (R t) (rotate (rotationExp φ) (a t))) t)
    (hw : ∀ t ∈ Icc 0 T, HasDerivAt w
      (Gravity.field3 μ (q t)+rotate (R t) (a t)) t)
    (hx : Continuous (fun t => coordinates φ (R t) (p t) (v t) (q t) (w t)))
    (hr : Continuous (fun t => remainder μ (R t) (q t) (ω t)
      (coordinates φ (R t) (p t) (v t) (q t) (w t))))
    (hc : Continuous (fun t => coefficient μ r D (q t) (ω t)))
    (hA : Continuous (fun t => operator μ (R t) (q t) (a t) (ω t)))
    (hB : Continuous B) (he : Continuous e)
    (he0 : ∀ t ∈ Icc 0 T, 0≤e t)
    (hdefect : ∀ t ∈ Icc 0 T, ‖operator μ (R t) (q t) (a t) (ω t)-B t‖≤e t)
    (hegain : ∀ t ∈ Icc 0 T,
      (∫ s in 0..t, ‖NearLinearTube.kernel Φ t s‖*e s)≤δ)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val)
      (B t*(Φ t).val) t)
    (hΦ₀ : Φ 0=1)
    (hi : ‖coordinates φ (R 0) (p 0) (v 0) (q 0) (w 0)‖≤α)
    (hlin : ∀ t ∈ Icc 0 T,
      ‖(Φ t).val (coordinates φ (R 0) (p 0) (v 0) (q 0) (w 0))‖≤α)
    (hgain : ∀ t ∈ Icc 0 T,
      (∫ s in 0..t, ‖NearLinearTube.kernel Φ t s‖*
        coefficient μ r D (q s) (ω s))≤β) :
    ∀ t ∈ Icc 0 T,
      ‖coordinates φ (R t) (p t) (v t) (q t) (w t)‖≤LinearQuadraticTube.radius α δ β ∧
      ‖coordinates φ (R t) (p t) (v t) (q t) (w t)-
        (Φ t).val (coordinates φ (R 0) (p 0) (v 0) (q 0) (w 0))‖≤
          δ*LinearQuadraticTube.radius α δ β+β*(LinearQuadraticTube.radius α δ β)^2 ∧
      enorm (p t-q t)≤D := by
  let x := fun t => coordinates φ (R t) (p t) (v t) (q t) (w t)
  have hchart : enorm φ<2*Real.pi := hφ.trans_lt (by linarith [Real.pi_gt_three])
  have hode (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt x
      (operator μ (R t) (q t) (a t) (ω t) (x t)+
        remainder μ (R t) (q t) (ω t) (x t)) t := by
    exact equation μ φ hchart (hR t ht) (hp t ht) (hq t ht) (hv t ht) (hw t ht)
  have hrem (t : ℝ) (ht : t ∈ Icc 0 T) (hb : ‖x t‖≤2*(α/(1-δ))) :
      ‖remainder μ (R t) (q t) (ω t) (x t)‖≤
        coefficient μ r D (q t) (ω t)*‖x t‖^2 := by
    apply remainder_quadratic μ hμ (R t) (q t) (ω t) (x t) hD (hqrad t ht)
    · linarith
    · exact hφ
  have result := ApproximateLinearTube.certificate Φ
    (fun t => operator μ (R t) (q t) (a t) (ω t)) B hΦ hΦ₀ x
    (fun t => remainder μ (R t) (q t) (ω t) (x t))
    e (fun t => coefficient μ r D (q t) (ω t))
    hT hα hδ0 hδ hβ hsmall hx hr hA hB he hc hode he0
    (fun t _ => coefficient_nonneg hμ (q t) (ω t)) hi hlin hdefect hrem hegain hgain
  intro t ht
  obtain ⟨htotal,herr⟩ := result t ht
  refine ⟨htotal,herr,?_⟩
  have hn : ‖x t‖≤2*(α/(1-δ)) := htotal.trans
    (LinearQuadraticTube.properties hα hδ hβ hsmall).2.1.le
  have he := reconstruction φ hchart (R t) (p t) (v t) (q t) (w t)
  have hpq : p t-q t=rotate (R t) (Jacobian.leftAt φ (x t 0)) := by
    change q t+rotate (R t) (Jacobian.leftAt φ (x t 0))=p t at he
    rw [←he]
    abel
  rw [hpq, rotate_enorm]
  apply (leftAt_nonexpansive φ (x t 0) hchart).trans
  have hn0 := (enorm_le_two_pi_norm (x t 0)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm (x t) 0) (by norm_num))
  linarith

/-- Output reconstruction charges an approximate reference position as well
as the transformed prediction error. Attitude is the same in both maps;
an approximate attitude would require an additional, separate bound. -/
theorem position_prediction_with_reference (φ : Vec3) (hφ : enorm φ<2*Real.pi)
    (R : SO3) (p v q w qhat : Vec3) (xhat : LogState) {ε η : ℝ}
    (he : ‖coordinates φ R p v q w-xhat‖≤ε) (hq : enorm (q-qhat)≤η) :
    enorm (p-(qhat+rotate R (Jacobian.leftAt φ (xhat 0))))≤2*ε+η := by
  have h := position_prediction_bound φ hφ R p v q w xhat he
  have hid : p-(qhat+rotate R (Jacobian.leftAt φ (xhat 0)))=
      (p-(q+rotate R (Jacobian.leftAt φ (xhat 0))))+(q-qhat) := by abel
  rw [hid]
  exact (enorm_add_le _ _).trans (add_le_add h hq)

end GNC.MountingOrbitalError
