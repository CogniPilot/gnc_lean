import GNC.Dynamics.MountingOrbitalBounds
import GNC.Analysis.NearLinearTube

/-! Continuous-time orbital certificates for a fixed body mounting error.
The physical ODE supplies the coordinate ODE; no log lift is assumed.
The exact STM, trajectory existence, and continuity are explicit hypotheses.
All quantities are dimensionless, with the native box norm on LogState.
-/
noncomputable section
open Set MeasureTheory
namespace GNC.MountingOrbitalError

abbrev End := LogState →L[ℝ] LogState

/-- Full inverse-square gravity plus a constant body-fixed mounting offset.
The quadratic closure proves its own position domain, including all times
between zero and T. Prescribed acceleration and angular rate may vary.
No claim about a numerically approximated STM is made by this theorem. -/
theorem certificate (μ : ℝ) (hμ : 0≤μ) (φ : Vec3) (hφ : enorm φ≤1)
    (R : ℝ → SO3) (p v q w a ω : ℝ → Vec3) (Φ : ℝ → Endˣ)
    {T α β r D : ℝ} (hT : 0≤T) (hα : 0<α) (hβ : 0≤β)
    (hsmall : 4*α*β<1) (hD : D<r) (hdom : 4*α≤D)
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
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val)
      (operator μ (R t) (q t) (a t) (ω t)*(Φ t).val) t)
    (hΦ₀ : Φ 0=1)
    (hi : ‖coordinates φ (R 0) (p 0) (v 0) (q 0) (w 0)‖≤α)
    (hlin : ∀ t ∈ Icc 0 T,
      ‖(Φ t).val (coordinates φ (R 0) (p 0) (v 0) (q 0) (w 0))‖≤α)
    (hgain : ∀ t ∈ Icc 0 T,
      (∫ s in 0..t, ‖NearLinearTube.kernel Φ t s‖*
        coefficient μ r D (q s) (ω s))≤β) :
    ∀ t ∈ Icc 0 T,
      ‖coordinates φ (R t) (p t) (v t) (q t) (w t)‖≤QuadraticTube.radius α β ∧
      ‖coordinates φ (R t) (p t) (v t) (q t) (w t)-
        (Φ t).val (coordinates φ (R 0) (p 0) (v 0) (q 0) (w 0))‖≤
          β*(QuadraticTube.radius α β)^2 ∧
      enorm (p t-q t)≤D := by
  let x := fun t => coordinates φ (R t) (p t) (v t) (q t) (w t)
  have hchart : enorm φ<2*Real.pi := hφ.trans_lt (by linarith [Real.pi_gt_three])
  have hode (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt x
      (operator μ (R t) (q t) (a t) (ω t) (x t)+
        remainder μ (R t) (q t) (ω t) (x t)) t := by
    exact equation μ φ hchart (hR t ht) (hp t ht) (hq t ht) (hv t ht) (hw t ht)
  have hrem (t : ℝ) (ht : t ∈ Icc 0 T) (hb : ‖x t‖≤2*α) :
      ‖remainder μ (R t) (q t) (ω t) (x t)‖≤
        coefficient μ r D (q t) (ω t)*‖x t‖^2 := by
    apply remainder_quadratic μ hμ (R t) (q t) (ω t) (x t) hD (hqrad t ht)
    · linarith
    · exact hφ
  have result := NearLinearTube.certificate Φ
    (fun t => operator μ (R t) (q t) (a t) (ω t)) hΦ hΦ₀ x
    (fun t => remainder μ (R t) (q t) (ω t) (x t))
    (fun t => coefficient μ r D (q t) (ω t))
    hT hα hβ hsmall hx hr hc hode
    (fun t _ => coefficient_nonneg hμ (q t) (ω t)) hi hlin hrem hgain
  intro t ht
  obtain ⟨htotal,herr⟩ := result t ht
  refine ⟨htotal,herr,?_⟩
  have hn : ‖x t‖≤2*α := htotal.trans
    (QuadraticTube.radius_properties hα hβ hsmall).2.1.le
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

/-- A bound in the transformed coordinates certifies an actual position
prediction reconstructed with the same mounting angle. This is a pointwise
statement for each allowed angle, hence usable uniformly over an angle set. -/
theorem position_prediction_bound (φ : Vec3) (hφ : enorm φ<2*Real.pi)
    (R : SO3) (p v q w : Vec3) (xhat : LogState) {ε : ℝ}
    (he : ‖coordinates φ R p v q w-xhat‖≤ε) :
    enorm (p-(q+rotate R (Jacobian.leftAt φ (xhat 0))))≤2*ε := by
  let x := coordinates φ R p v q w
  have hrec := reconstruction φ hφ R p v q w
  have hp : p-(q+rotate R (Jacobian.leftAt φ (xhat 0)))=
      rotate R (Jacobian.leftAt φ (x 0)-Jacobian.leftAt φ (xhat 0)) := by
    rw [←hrec, rotate_sub]
    dsimp [x]
    abel
  rw [hp, rotate_enorm]
  apply (MountingErrorCoordinates.output_error φ (x 0) (xhat 0) hφ).trans
  have hn := enorm_le_two_pi_norm (x 0-xhat 0)
  have hb := norm_le_pi_norm (x-xhat) 0
  change ‖x 0-xhat 0‖≤‖x-xhat‖ at hb
  change ‖x-xhat‖≤ε at he
  linarith

end GNC.MountingOrbitalError
