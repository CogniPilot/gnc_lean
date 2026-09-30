import GNC.Preintegration.FohInputError
import GNC.Analysis.EuclideanOperatorIsometry

/-! A posteriori certificates for arbitrary finite inertial predictors.
The predictor rotation need not be orthogonal. Transport by the true rotation
removes its skew generator before bounding the defect. There is no exponential
growth allowance in the common angular rate. -/
noncomputable section
open Set
namespace GNC.Preintegration.CenteredFoh.Defect
open InputError GNC.EuclideanOperator

theorem transported_error_derivative (R : ℝ → SO3) (Q d : ℝ → Op)
    (ω : ℝ → Vec3) (t : ℝ)
    (hR : HasDerivAt (fun s => rotation (R s)) (rotation (R t)*hat (ω t)) t)
    (hQ : HasDerivAt Q (Q t*hat (ω t)+d t) t) :
    HasDerivAt (fun s => (rotation (R s)-Q s)*star (rotation (R s)))
      (-d t*star (rotation (R t))) t := by
  convert (hR.sub hQ).mul hR.star using 1
  rw [StarMul.star_mul (rotation (R t)) (hat (ω t)), star_hat]
  change -d t*star (rotation (R t)) =
    (rotation (R t)*hat (ω t)-(Q t*hat (ω t)+d t))*star (rotation (R t))+
      (rotation (R t)-Q t)*(-hat (ω t)*star (rotation (R t)))
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, map_neg]
  abel

/-- An arbitrary rotation defect is integrated in Frobenius norm; the finite
matrix Q need not lie on SO(3) or satisfy a small-step condition. -/
theorem rotation_defect_bound {H : ℝ} (R : ℝ → SO3) (Q d : ℝ → Op)
    (ω : ℝ → Vec3) (q b : ℝ → ℝ)
    (hR : ∀ t ∈ Icc 0 H,
      HasDerivAt (fun s => rotation (R s)) (rotation (R t)*hat (ω t)) t)
    (hQ : ∀ t ∈ Icc 0 H, HasDerivAt Q (Q t*hat (ω t)+d t) t)
    (h0 : Q 0 = rotation (R 0)) (hq0 : q 0 = 0)
    (hq : ∀ t, HasDerivAt q (b t) t)
    (hb : ∀ t ∈ Icc 0 H, frobenius (d t) ≤ b t) :
    ∀ t ∈ Icc 0 H, frobenius (rotation (R t)-Q t) ≤ q t := by
  have hiso (t : ℝ) (L : Op) :
      frobenius (L*star (rotation (R t))) = frobenius L :=
    frobenius_mul_right L _ (fun x => by
      rw [star_star (rotation (R t))]
      exact rotation_norm_apply (R t) x)
  let e := fun t => (rotation (R t)-Q t)*star (rotation (R t))
  let ed := fun t => -d t*star (rotation (R t))
  have hd (t : ℝ) (ht : t ∈ Icc 0 H) :
      HasDerivAt (fun s => columnsCLM 3 (e s)) (columnsCLM 3 (ed t)) t := by
    exact (columnsCLM 3).hasFDerivAt.comp_hasDerivAt t
      (transported_error_derivative R Q d ω t (hR t ht) (hQ t ht))
  have hi : columnsCLM 3 (e 0) = 0 := by
    have he0 : e 0 = 0 := by
      dsimp [e]
      rw [h0, sub_self, zero_mul]
    rw [he0, map_zero]
  have hn (t : ℝ) (ht : t ∈ Icc 0 H) : ‖columnsCLM 3 (ed t)‖ ≤ b t := by
    change frobenius (-d t*star (rotation (R t))) ≤ b t
    rw [hiso, EuclideanOperator.frobenius_neg]
    exact hb t ht
  have hh := norm_le_primitive (fun t => columnsCLM 3 (e t))
    (fun t => columnsCLM 3 (ed t)) q b hd hq hi hq0 hn
  intro t ht
  have hb' : EuclideanOperator.frobenius (e t) ≤ q t := hh t ht
  change EuclideanOperator.frobenius ((rotation (R t)-Q t)*star (rotation (R t))) ≤ q t at hb'
  rw [hiso] at hb'
  exact hb'

/-- Three physical defect envelopes yield three scalar primitive budgets.
The trajectory and finite predictors satisfy the stated ODEs; the error
budgets are conclusions, not envelopes assumed of the unknown solution. -/
theorem physical_defect_bound {H scale : ℝ} (hscale : 0 ≤ scale)
    (R : ℝ → SO3) (Qr dr : ℝ → Op)
    (v Qv p Qp u dv dp : ℝ → E3) (ω : ℝ → Vec3)
    (qr qv qp br bv bp abar : ℝ → ℝ)
    (hR : ∀ t ∈ Icc 0 H,
      HasDerivAt (fun s => rotation (R s)) (rotation (R t)*hat (ω t)) t)
    (hQr : ∀ t ∈ Icc 0 H, HasDerivAt Qr (Qr t*hat (ω t)+dr t) t)
    (hv : ∀ t ∈ Icc 0 H, HasDerivAt v (rotation (R t) (u t)) t)
    (hQv : ∀ t ∈ Icc 0 H, HasDerivAt Qv (Qr t (u t)+dv t) t)
    (hp : ∀ t ∈ Icc 0 H, HasDerivAt p (scale • v t) t)
    (hQp : ∀ t ∈ Icc 0 H, HasDerivAt Qp (scale • Qv t+dp t) t)
    (hR0 : Qr 0 = rotation (R 0)) (hv0 : v 0 = Qv 0) (hp0 : p 0 = Qp 0)
    (hqr0 : qr 0 = 0) (hqv0 : qv 0 = 0) (hqp0 : qp 0 = 0)
    (hqr : ∀ t, HasDerivAt qr (br t) t)
    (hqv : ∀ t, HasDerivAt qv (qr t*abar t+bv t) t)
    (hqp : ∀ t, HasDerivAt qp (scale*qv t+bp t) t)
    (hbr : ∀ t ∈ Icc 0 H, frobenius (dr t) ≤ br t)
    (hbv : ∀ t ∈ Icc 0 H, ‖dv t‖ ≤ bv t)
    (hbp : ∀ t ∈ Icc 0 H, ‖dp t‖ ≤ bp t)
    (hbar : ∀ t ∈ Icc 0 H, ‖u t‖ ≤ abar t) :
    ∀ t ∈ Icc 0 H, frobenius (rotation (R t)-Qr t) ≤ qr t ∧
      ‖v t-Qv t‖ ≤ qv t ∧ ‖p t-Qp t‖ ≤ qp t := by
  have hr := rotation_defect_bound R Qr dr ω qr br hR hQr hR0 hqr0 hqr hbr
  have hvb := norm_le_primitive (fun t => v t-Qv t)
    (fun t => (rotation (R t)-Qr t) (u t)-dv t) qv
    (fun t => qr t*abar t+bv t)
    (fun t ht => by
      convert (hv t ht).sub (hQv t ht) using 1
      simp only [ContinuousLinearMap.sub_apply]
      abel)
    hqv (by simp [hv0]) hqv0 (fun t ht => by
      have hqrn : 0 ≤ qr t := (norm_nonneg _).trans (hr t ht)
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_apply_le_frobenius _ _).trans
          (mul_le_mul (hr t ht) (hbar t ht) (norm_nonneg _) hqrn)) (hbv t ht)))
  have hpb := norm_le_primitive (fun t => p t-Qp t)
    (fun t => scale • (v t-Qv t)-dp t) qp (fun t => scale*qv t+bp t)
    (fun t ht => by
      convert (hp t ht).sub (hQp t ht) using 1
      simp only [smul_sub]
      abel)
    hqp (by simp [hp0]) hqp0 (fun t ht => by
      apply (norm_sub_le _ _).trans
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
      exact add_le_add (mul_le_mul_of_nonneg_left (hvb t ht) hscale) (hbp t ht))
  exact fun t ht => ⟨hr t ht, hvb t ht, hpb t ht⟩

end GNC.Preintegration.CenteredFoh.Defect
