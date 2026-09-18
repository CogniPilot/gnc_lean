import GNC.Analysis.FirstOrderCertificate
import GNC.Applications.DroneCertificate
import GNC.Analysis.TimeDependentODE
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! The drag instance: a nonlinear, velocity-dependent field. On the 2 s
jet-drone ascent the speed obeys `v' = T(F cosθ/m − g0) − T c_d v²/m`
(first order, with `v²` exact on the ascent), with the tilt
`|θ| ≤ π/36` as the parameter. The no-drag variable-mass predictor is
certified against the drag field: neglecting drag costs at most 0.7698 m/s
at the horizon. Existence comes from the clipped field through
`BoundedODE`; the coarse ramps prove the clip inactive. -/
noncomputable section
namespace GNC.DragCertificate
open Set FirstOrderCertificate
open scoped NNReal
open DroneCertificate

/-- Burn horizon (s). -/ def T : ℝ := 2
/-- Thrust force (N). -/ def F : ℝ := 200
/-- Gravity (m/s^2). -/ def g0 : ℝ := 981/100
/-- Drag coefficient (kg/m). -/ def cd : ℝ := 1/50
/-- Initial mass (kg). -/ def mi : ℝ := 12
/-- Tilt cosine lower bound (rational enclosure of cos(π/36)). -/ def c0 : ℝ := 996/1000

/-- Mass along the burn, clamped outside [0,1]. -/
def mass (t : ℝ) : ℝ := mi - (1/5) * tc t
/-- Reciprocal mass. -/
def wM (t : ℝ) : ℝ := 1 / mass t

theorem mass_ge (t : ℝ) : (59/5 : ℝ) ≤ mass t := by
  have h := (tc_mem t).2
  have hle : (1/5 : ℝ) * tc t ≤ 1/5 :=
    calc (1/5 : ℝ) * tc t ≤ (1/5) * 1 := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 1/5 := mul_one _
  simp only [mass, mi]; linarith

theorem mass_le (t : ℝ) : mass t ≤ 12 := by
  have h := (tc_mem t).1
  have h0 : (0:ℝ) ≤ (1/5) * tc t := mul_nonneg (by norm_num) h
  simp only [mass, mi]; linarith

theorem mass_pos (t : ℝ) : 0 < mass t := by
  have h := mass_ge t; norm_num at *; linarith

theorem mass_continuous : Continuous mass :=
  continuous_const.sub (continuous_const.mul tc_continuous)

theorem wM_continuous : Continuous wM := by
  show Continuous fun t : ℝ => (1:ℝ) / mass t
  exact Continuous.div₀ continuous_const mass_continuous (fun t => ne_of_gt (mass_pos t))

theorem wM_ge (t : ℝ) : (1/12 : ℝ) ≤ wM t := by
  have h1 : (0:ℝ) < mass t := mass_pos t
  have h2 : mass t ≤ 12 := mass_le t
  rw [wM]
  exact one_div_le_one_div_of_le h1 h2

theorem wM_le (t : ℝ) : wM t ≤ 5/59 := by
  have h1 : (0:ℝ) < 59/5 := by norm_num
  have h2 : (59/5 : ℝ) ≤ mass t := mass_ge t
  rw [wM]
  calc (1:ℝ)/mass t ≤ 1/(59/5) := one_div_le_one_div_of_le h1 h2
    _ = 5/59 := by norm_num

theorem wM_nonneg (t : ℝ) : (0:ℝ) ≤ wM t := by
  have h := wM_ge t; linarith

/-- Velocity clamp: the drag model saturates above 15 m/s and at 0. -/
def clipV (v : ℝ) : ℝ := (projIcc (0:ℝ) (15:ℝ) (by norm_num) v : ℝ)

theorem clipV_mem (v : ℝ) : clipV v ∈ Icc (0:ℝ) 15 := by
  have h := (projIcc (0:ℝ) (15:ℝ) (by norm_num) v).property
  simpa [clipV] using h

theorem clipV_id {v : ℝ} (hv : v ∈ Icc (0:ℝ) 15) : clipV v = v := by
  simp [clipV, projIcc_of_mem _ hv]

theorem clipV_lipschitz : LipschitzWith 1 clipV := by
  have h := isometry_subtype_coe.lipschitz.comp
    (LipschitzWith.projIcc (show (0:ℝ) ≤ 15 by norm_num))
  simpa [clipV] using h

/-- The first-order speed field (normalized time), clipped drag. -/
def field (θ t v : ℝ) : ℝ :=
  T * (F * Real.cos θ * wM t - g0 - cd * (clipV v)^2 * wM t)

theorem field_lipschitz (θ t : ℝ) : LipschitzWith (6/59 : ℝ≥0) (field θ t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hclip := clipV_lipschitz.dist_le_mul x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hclip
  have hx0 : 0 ≤ clipV x := (clipV_mem x).1
  have hx1 : clipV x ≤ 15 := (clipV_mem x).2
  have hy1 : clipV y ≤ 15 := (clipV_mem y).2
  have hy0 : 0 ≤ clipV y := (clipV_mem y).1
  have hsum : |clipV x + clipV y| ≤ 30 := by
    rw [abs_of_nonneg (add_nonneg hx0 hy0)]; linarith
  have hdiff : |(clipV x)^2 - (clipV y)^2| ≤ 30 * |clipV x - clipV y| := by
    have h : (clipV x)^2 - (clipV y)^2 = (clipV x + clipV y) * (clipV x - clipV y) := by
      ring
    rw [h, abs_mul]
    exact mul_le_mul hsum (le_refl (|clipV x - clipV y|)) (abs_nonneg _) (by norm_num)
  have hw := wM_nonneg t
  have hw' := wM_le t
  have hTc : (0:ℝ) ≤ T * cd := by rw [T, cd]; norm_num
  simp only [field, dist_eq_norm]
  rw [show T * (F * Real.cos θ * wM t - g0 - cd * (clipV x)^2 * wM t) -
      T * (F * Real.cos θ * wM t - g0 - cd * (clipV y)^2 * wM t) =
      -(T * cd * wM t) * ((clipV x)^2 - (clipV y)^2) by ring]
  simp only [Real.norm_eq_abs]
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hTc, abs_of_nonneg hw]
  simp only [T, cd]
  rw [show ((2:ℝ) * (1/50)) * wM t * |(clipV x)^2 - (clipV y)^2| =
      ((2 * (1/50)) * wM t) * |(clipV x)^2 - (clipV y)^2| by ring]
  calc ((2 * (1/50)) * wM t) * |(clipV x)^2 - (clipV y)^2|
      ≤ ((2 * (1/50)) * (5/59)) * (30 * |clipV x - clipV y|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hw' hTc) hdiff (abs_nonneg _)
          (mul_nonneg hTc (by norm_num))
    _ ≤ (6/59 : ℝ) * |x - y| := by
        rw [show (6/59 : ℝ) * |x - y| =
            ((2 * (1/50)) * (5/59)) * (30 * |clipV x - clipV y|) +
            (6/59) * (|x - y| - |clipV x - clipV y|) by ring]
        have hrest : (0:ℝ) ≤ (6/59) * (|x - y| - |clipV x - clipV y|) := by
          apply mul_nonneg (by norm_num)
          have habs : |clipV x - clipV y| ≤ |x - y| := by
            have h2 := clipV_lipschitz.dist_le_mul x y
            rwa [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm,
              Real.norm_eq_abs, Real.norm_eq_abs] at h2
          linarith
        linarith

theorem field_bound (θ t v : ℝ) : ‖field θ t v‖ ≤ 5429/100 := by
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hw : (0:ℝ) ≤ wM t := wM_nonneg t
  have hw' : wM t ≤ 5/59 := wM_le t
  have hc2 : (0:ℝ) ≤ (clipV v)^2 := by positivity
  have hc2' : (clipV v)^2 ≤ 225 := by
    have h := (clipV_mem v).2
    have h0 := (clipV_mem v).1
    calc (clipV v)^2 ≤ 15^2 := pow_le_pow_left₀ h0 h 2
      _ = 225 := by norm_num
  rw [Real.norm_eq_abs]
  have hg0 : |g0| = g0 := abs_of_nonneg (by norm_num [g0])
  have hA : |F * Real.cos θ * wM t| ≤ 200 * (5/59) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num [F] : (0:ℝ) ≤ F),
      abs_of_nonneg hw]
    simp only [F]
    have h1 : (200:ℝ) * |Real.cos θ| ≤ 200 := by
      simpa using mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ) ≤ 200)
    exact mul_le_mul h1 hw' hw (by norm_num)
  have hC : |cd * (clipV v)^2 * wM t| ≤ (1/50) * 225 * (5/59) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num [cd] : (0:ℝ) ≤ cd),
      abs_of_nonneg hc2, abs_of_nonneg hw]
    simp only [cd]
    have h1 : (1/50:ℝ) * (clipV v)^2 ≤ (1/50) * 225 :=
      mul_le_mul_of_nonneg_left hc2' (by norm_num)
    exact mul_le_mul h1 hw' hw (by norm_num)
  calc |T * (F * Real.cos θ * wM t - g0 - cd * (clipV v)^2 * wM t)|
      = T * |F * Real.cos θ * wM t - g0 - cd * (clipV v)^2 * wM t| := by
        rw [abs_mul, abs_of_nonneg (by norm_num [T] : (0:ℝ) ≤ T)]
    _ ≤ T * (|F * Real.cos θ * wM t| + |g0| + |cd * (clipV v)^2 * wM t|) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num [T] : (0:ℝ) ≤ T)
        have h1 := abs_sub (F * Real.cos θ * wM t) (g0 + cd * (clipV v)^2 * wM t)
        have h2 := abs_add_le g0 (cd * (clipV v)^2 * wM t)
        have h3 : F * Real.cos θ * wM t - g0 - cd * (clipV v)^2 * wM t =
            F * Real.cos θ * wM t - (g0 + cd * (clipV v)^2 * wM t) := by ring
        rw [h3]
        linarith
    _ = T * (|F * Real.cos θ * wM t| + g0 + |cd * (clipV v)^2 * wM t|) := by
        rw [hg0]
    _ ≤ T * (200 * (5/59) + g0 + (1/50) * 225 * (5/59)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num [T])
        exact add_le_add (add_le_add hA (le_refl _)) hC
    _ ≤ 5429/100 := by simp only [T, g0]; norm_num

theorem field_continuous (θ : ℝ) :
    Continuous (fun z : ℝ × ℝ => field θ z.1 z.2) := by
  have hwM1 : Continuous (fun z : ℝ × ℝ => wM z.1) :=
    wM_continuous.comp continuous_fst
  have hA : Continuous (fun z : ℝ × ℝ => F * Real.cos θ * wM z.1) :=
    (continuous_const.mul continuous_const).mul hwM1
  have hC : Continuous (fun z : ℝ × ℝ => cd * (clipV z.2)^2 * wM z.1) :=
    (continuous_const.mul ((clipV_lipschitz.continuous.comp continuous_snd).pow 2)).mul
      hwM1
  show Continuous (fun z : ℝ × ℝ => T * (F * Real.cos θ * wM z.1 - g0 -
    cd * (clipV z.2)^2 * wM z.1))
  exact continuous_const.mul ((hA.sub continuous_const).sub hC)

/-- Coarse upper ramp: drag only decelerates. -/
theorem field_le_upper (θ t v : ℝ) : field θ t v ≤ 357/25 := by
  have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hw : (0:ℝ) ≤ wM t := wM_nonneg t
  have hw' : wM t ≤ 5/59 := wM_le t
  have hA : (200:ℝ) * Real.cos θ * wM t ≤ 200 * (5/59) := by
    have h1 : (200:ℝ) * Real.cos θ ≤ 200 * 1 :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    rw [mul_one] at h1
    exact mul_le_mul h1 hw' hw (by norm_num)
  have hC : (0:ℝ) ≤ (1/50) * (clipV v)^2 * wM t :=
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hw
  simp only [field, T, F, g0, cd]
  linarith [hA, hC]

/-- Coarse lower ramp, valid on the ascent (uses the clip cap). -/
theorem field_ge_lower {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36))
    (t v : ℝ) : (1281/100 : ℝ) ≤ field θ t v := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  obtain ⟨h1, h2⟩ := hθ
  have habs : |θ| ≤ Real.pi/36 := by
    rw [abs_le]; constructor <;> linarith
  have hpi36 : Real.pi/36 ≤ 7/80 := by linarith
  have hsq : θ^2 ≤ (7/80)^2 := by
    have hp0 : (0:ℝ) ≤ Real.pi/36 := by have := Real.pi_pos; linarith
    have h3 := pow_le_pow_left₀ (abs_nonneg θ) habs 2
    rw [sq_abs] at h3
    exact h3.trans (pow_le_pow_left₀ hp0 hpi36 2)
  have hcos : (996/1000 : ℝ) ≤ Real.cos θ := by
    have h := Real.one_sub_sq_div_two_le_cos (x := θ)
    linarith
  have hw : (1/12 : ℝ) ≤ wM t := wM_ge t
  have hw' : wM t ≤ 5/59 := wM_le t
  have hcpos : (0:ℝ) ≤ Real.cos θ := by linarith
  have hA : (200:ℝ) * ((996/1000) * (1/12)) ≤ 200 * Real.cos θ * wM t := by
    have hcF : (200:ℝ) * (996/1000) ≤ 200 * Real.cos θ :=
      mul_le_mul_of_nonneg_left hcos (by norm_num)
    have h1 : (200 * (996/1000)) * (1/12) ≤ (200 * Real.cos θ) * wM t := by
      have hF0 : (0:ℝ) ≤ 200 * Real.cos θ := mul_nonneg (by norm_num) hcpos
      exact mul_le_mul hcF hw (by norm_num) hF0
    calc (200:ℝ) * ((996/1000) * (1/12)) = (200 * (996/1000)) * (1/12) := by ring
      _ ≤ (200 * Real.cos θ) * wM t := h1
  have hC : (1/50:ℝ) * (clipV v)^2 * wM t ≤ (1/50) * 225 * (5/59) := by
    have hc2 : (clipV v)^2 ≤ 225 := by
      have h := (clipV_mem v).2; have h0 := (clipV_mem v).1
      calc (clipV v)^2 ≤ 15^2 := pow_le_pow_left₀ h0 h 2
        _ = 225 := by norm_num
    have h1 : (clipV v)^2 * wM t ≤ 225 * (5/59) := by
      have hc20 : (0:ℝ) ≤ (clipV v)^2 := by positivity
      exact mul_le_mul hc2 hw' (wM_nonneg t) (by norm_num)
    calc (1/50:ℝ) * (clipV v)^2 * wM t = (1/50) * ((clipV v)^2 * wM t) := by ring
      _ ≤ (1/50) * (225 * (5/59)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (1/50) * 225 * (5/59) := by ring
  simp only [field, T, F, g0, cd]
  linarith [hA, hC]

/-- The integrated degree-five reciprocal-mass series (rational polynomial). -/
def wInt5 (t : ℝ) : ℝ :=
  (1/12)*t + (1/1440)*t^2 + (1/129600)*t^3 + (1/10368000)*t^4 +
    (1/777600000)*t^5 + (1/55987200000)*t^6
/-- Its derivative, the degree-five truncation of the reciprocal mass. -/
def w5 (t : ℝ) : ℝ :=
  (1/12) * (1 + t/60 + (t/60)^2 + (t/60)^3 + (t/60)^4 + (t/60)^5)

/-- The no-drag variable-mass speed candidate. -/
def q (θ t : ℝ) : ℝ := T * (F * Real.cos θ * wInt5 t - g0 * t)
/-- Its derivative. -/
def qd (θ t : ℝ) : ℝ := T * (F * Real.cos θ * w5 t - g0)

theorem wInt5_hasDeriv (t : ℝ) : HasDerivAt wInt5 (w5 t) t := by
  unfold wInt5 w5
  have h := (((((hasDerivAt_id t).const_mul (1/12)).add
    (((hasDerivAt_pow 2 t).const_mul (1/1440)))).add
    (((hasDerivAt_pow 3 t).const_mul (1/129600)))).add
    (((hasDerivAt_pow 4 t).const_mul (1/10368000)))).add
    (((hasDerivAt_pow 5 t).const_mul (1/777600000)))
  have h6 := h.add (((hasDerivAt_pow 6 t).const_mul (1/55987200000)))
  exact h6.congr_deriv (by
    rw [show (2:ℕ)-1 = 1 by decide, show (3:ℕ)-1 = 2 by decide,
      show (4:ℕ)-1 = 3 by decide, show (5:ℕ)-1 = 4 by decide,
      show (6:ℕ)-1 = 5 by decide]
    ring)

theorem q_hasDeriv (θ t : ℝ) : HasDerivAt (q θ) (qd θ t) t := by
  show HasDerivAt (fun t => T * (F * Real.cos θ * wInt5 t - g0 * t))
    (T * (F * Real.cos θ * w5 t - g0)) t
  exact ((wInt5_hasDeriv t).const_mul (F * Real.cos θ)).sub
    ((hasDerivAt_id t).const_mul g0) |>.const_mul T |>.congr_deriv (by ring)

theorem q_zero (θ : ℝ) : q θ 0 = 0 := by simp [q, wInt5, T]

/-- The integrated truncation, bounded by (5/59) t on the horizon. -/
theorem wInt5_le (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : wInt5 t ≤ (5/59) * t := by
  have ht0 : (0:ℝ) ≤ t := ht.1
  have hpow : ∀ k : ℕ, 1 ≤ k → t^k ≤ t := by
    intro k hk
    have h := pow_le_of_le_one ht0 ht.2 (show k ≠ 0 by omega)
    exact h
  have hterm : wInt5 t ≤ t * (1/12 + 1/1440 + 1/129600 + 1/10368000 +
      1/777600000 + 1/55987200000) := by
    unfold wInt5
    nlinarith [hpow 2 (by norm_num), hpow 3 (by norm_num), hpow 4 (by norm_num),
      hpow 5 (by norm_num), hpow 6 (by norm_num), ht0]
  have hconst : (1/12 + 1/1440 + 1/129600 + 1/10368000 + 1/777600000 +
      1/55987200000 : ℝ) ≤ 5/59 := by norm_num
  exact hterm.trans (by
    rw [mul_comm (5/59 : ℝ) t]
    exact mul_le_mul_of_nonneg_left hconst ht0)

theorem wInt5_ge (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : t/12 ≤ wInt5 t := by
  have ht0 : (0:ℝ) ≤ t := ht.1
  unfold wInt5
  nlinarith [pow_nonneg ht0 2, pow_nonneg ht0 3, pow_nonneg ht0 4,
    pow_nonneg ht0 5, pow_nonneg ht0 6]

theorem wInt5_nonneg (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ wInt5 t := by
  have h := wInt5_ge t ht
  have ht0 := ht.1
  linarith

/-- Candidate bounds on the horizon. -/
theorem q_bounds {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36))
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ q θ t ∧ q θ t ≤ 143/10 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  obtain ⟨h1, h2⟩ := hθ
  have habs : |θ| ≤ Real.pi/36 := by
    rw [abs_le]; constructor <;> linarith
  have hpi36 : Real.pi/36 ≤ 7/80 := by linarith
  have hsq : θ^2 ≤ (7/80)^2 := by
    have hp0 : (0:ℝ) ≤ Real.pi/36 := by have := Real.pi_pos; linarith
    have h3 := pow_le_pow_left₀ (abs_nonneg θ) habs 2
    rw [sq_abs] at h3
    exact h3.trans (pow_le_pow_left₀ hp0 hpi36 2)
  have hcos : (996/1000 : ℝ) ≤ Real.cos θ := by
    have h := Real.one_sub_sq_div_two_le_cos (x := θ)
    linarith
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have ht0 : (0:ℝ) ≤ t := ht.1
  have hwInt0 := wInt5_nonneg t ht
  have hwInt := wInt5_le t ht
  have hge12 : t/12 ≤ wInt5 t := wInt5_ge t ht
  constructor
  · have hcpos : (0:ℝ) ≤ Real.cos θ := by linarith
    have hAl : (200:ℝ) * ((996/1000) * (t/12)) ≤ 200 * Real.cos θ * wInt5 t := by
      have hcF : (200:ℝ) * (996/1000) ≤ 200 * Real.cos θ :=
        mul_le_mul_of_nonneg_left hcos (by norm_num)
      have h1 : (200 * (996/1000)) * (t/12) ≤ (200 * Real.cos θ) * wInt5 t := by
        have hF0 : (0:ℝ) ≤ 200 * Real.cos θ := mul_nonneg (by norm_num) hcpos
        have ht12 : (0:ℝ) ≤ t/12 := by positivity
        exact mul_le_mul hcF hge12 ht12 hF0
      calc (200:ℝ) * ((996/1000) * (t/12)) = (200 * (996/1000)) * (t/12) := by ring
        _ ≤ (200 * Real.cos θ) * wInt5 t := h1
    simp only [q, T, F, g0]
    nlinarith [hAl, ht0]
  · have hAu : (200:ℝ) * Real.cos θ * wInt5 t ≤ (1000/59) * t := by
      have hcF : (200:ℝ) * Real.cos θ ≤ 200 := by
        have h := mul_le_mul_of_nonneg_left hc1 (by norm_num : (0:ℝ) ≤ 200)
        simpa using h
      have h1 : (200 * Real.cos θ) * wInt5 t ≤ 200 * ((5/59) * t) :=
        mul_le_mul hcF hwInt hwInt0 (by norm_num)
      calc (200:ℝ) * Real.cos θ * wInt5 t = (200 * Real.cos θ) * wInt5 t := rfl
        _ ≤ 200 * ((5/59) * t) := h1
        _ = (1000/59) * t := by ring
    simp only [q, T, F, g0]
    have hpos : (0:ℝ) ≤ (1000/59 - 981/100) * t :=
      mul_nonneg (by norm_num) ht0
    nlinarith [hAu, ht.2, hpos]

/-- The explicit six-term tail identity. -/
theorem tail_identity6 {x : ℝ} (hx : x ≠ 1) :
    1/(1-x) - (1 + x + x^2 + x^3 + x^4 + x^5) = x^6/(1-x) := by
  have h1 : (1:ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp [h1]
  ring

/-- The tail of the reciprocal-mass truncation. -/
theorem wM_sub_w5 (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    wM t - w5 t = (1/12) * ((t/60)^6 / (1 - t/60)) := by
  have hm : mass t = 12 * (1 - t/60) := by
    simp only [mass, mi, tc_eq t ht]; ring
  have hw : wM t = (1/12) * (1/(1 - t/60)) := by
    rw [wM, hm, div_mul_div_comm, one_mul]
  have hx : (t/60 : ℝ) ≠ 1 := by have h := ht.2; linarith
  rw [hw, w5]
  rw [← mul_sub]
  congr 1
  exact tail_identity6 hx

/-- The first-order defect of the no-drag candidate against the drag field. -/
theorem defect_bound {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36))
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    |field θ t (q θ t) - qd θ t| ≤ 6932/10000 := by
  obtain ⟨hq0, hq1⟩ := q_bounds hθ t ht
  have hw := wM_le t
  have htail : wM t - w5 t ≤ (1/12) * ((1/60)^6 / (59/60)) := by
    rw [wM_sub_w5 t ht]
    have hx0 : (0:ℝ) ≤ t/60 := by have h := ht.1; linarith
    have hx1 : t/60 ≤ 1/60 := by have h := ht.2; linarith
    have hp : (t/60)^6 ≤ (1/60)^6 := pow_le_pow_left₀ hx0 hx1 6
    have hd' : (59/60 : ℝ) ≤ 1 - t/60 := by have h := ht.2; linarith
    have hdiv : (t/60)^6 / (1 - t/60) ≤ (1/60)^6 / (59/60) :=
      div_le_div₀ (by positivity) hp (by norm_num) hd'
    exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have hfield : field θ t (q θ t) - qd θ t =
      T * (F * Real.cos θ * (wM t - w5 t) - cd * (q θ t)^2 * wM t) := by
    simp only [field, qd]; rw [clipV_id ⟨hq0, by linarith⟩]; ring
  rw [hfield]
  have hA : |T * F * Real.cos θ * (wM t - w5 t)| ≤
      2 * 200 * ((1/12) * ((1/60)^6 / (59/60))) := by
    have hnn : (0:ℝ) ≤ wM t - w5 t := by
      rw [wM_sub_w5 t ht]
      have hd : (0:ℝ) ≤ 1 - t/60 := by have h := ht.2; linarith
      positivity
    have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hnn' : (0:ℝ) ≤ T * F * Real.cos θ * (wM t - w5 t) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num [T]) (by norm_num [F]))
        (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by
          obtain ⟨h1, h2⟩ := hθ; have hpi := Real.pi_pos; linarith) (by
          obtain ⟨h1, h2⟩ := hθ; have hpi := Real.pi_pos; linarith))) hnn
    rw [abs_of_nonneg hnn']
    calc T * F * Real.cos θ * (wM t - w5 t)
        = ((2:ℝ) * 200 * Real.cos θ) * (wM t - w5 t) := by simp [T, F]
      _ ≤ ((2:ℝ) * 200 * 1) * ((1/12) * ((1/60)^6 / (59/60))) := by
          apply mul_le_mul _ htail hnn (by norm_num)
          have hcF : (2:ℝ) * 200 * Real.cos θ ≤ 2 * 200 * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2 * 200)
            exact hc
          simpa using hcF
      _ = 2 * 200 * ((1/12) * ((1/60)^6 / (59/60))) := by ring
  have hC : |T * cd * (q θ t)^2 * wM t| ≤ 2 * (1/50) * (143/10)^2 * (5/59) := by
    have hnn : (0:ℝ) ≤ cd * (q θ t)^2 :=
      mul_nonneg (by norm_num [cd]) (by positivity)
    have hnn' : (0:ℝ) ≤ T * cd * (q θ t)^2 * wM t := by
      apply mul_nonneg _ (wM_nonneg t)
      exact mul_nonneg (mul_nonneg (by norm_num [T]) (by norm_num [cd]))
        (by positivity)
    rw [abs_of_nonneg hnn']
    calc T * cd * (q θ t)^2 * wM t
        = (2:ℝ) * ((1/50) * ((q θ t)^2 * wM t)) := by simp [T, cd]; ring
      _ ≤ 2 * ((1/50) * ((143/10)^2 * (5/59))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/50)
          have hq2 : (q θ t)^2 ≤ (143/10)^2 := pow_le_pow_left₀ hq0 hq1 2
          exact mul_le_mul hq2 hw (wM_nonneg t) (by norm_num)
      _ = 2 * (1/50) * (143/10)^2 * (5/59) := by ring
  calc |T * (F * Real.cos θ * (wM t - w5 t) - cd * (q θ t)^2 * wM t)|
      ≤ |T * F * Real.cos θ * (wM t - w5 t)| + |T * cd * (q θ t)^2 * wM t| := by
        rw [show T * (F * Real.cos θ * (wM t - w5 t) - cd * (q θ t)^2 * wM t) =
            T * F * Real.cos θ * (wM t - w5 t) - T * cd * (q θ t)^2 * wM t by ring]
        exact abs_sub _ _
    _ ≤ 2 * 200 * ((1/12) * ((1/60)^6 / (59/60))) +
        2 * (1/50) * (143/10)^2 * (5/59) := add_le_add hA hC
    _ ≤ 6932/10000 := by norm_num

/-- The error derivative bound on the ascent. -/
theorem field_diff_bound {θ : ℝ} (v : ℝ) (hv : v ∈ Icc (0:ℝ) 15)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (hq : q θ t ∈ Icc (0:ℝ) (143/10)) :
    |field θ t v - field θ t (q θ t)| ≤ (9933/100000) * |v - q θ t| := by
  simp only [field]
  rw [clipV_id hv, clipV_id ⟨hq.1, by linarith [hq.2]⟩]
  have hw : (0:ℝ) ≤ wM t := wM_nonneg t
  have hw' : wM t ≤ 5/59 := wM_le t
  have hsum : |v + q θ t| ≤ 15 + 143/10 := by
    rw [abs_of_nonneg (add_nonneg hv.1 hq.1)]; linarith [hv.2, hq.2]
  rw [show T * (F * Real.cos θ * wM t - g0 - cd * v^2 * wM t) -
      T * (F * Real.cos θ * wM t - g0 - cd * (q θ t)^2 * wM t) =
      -(T * cd * wM t) * (v^2 - (q θ t)^2) by ring]
  have hTc : (0:ℝ) ≤ T * cd := by simp only [T, cd]; norm_num
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hTc, abs_of_nonneg hw]
  have hp : |v^2 - (q θ t)^2| ≤ (15 + 143/10) * |v - q θ t| := by
    rw [show v^2 - (q θ t)^2 = (v + q θ t) * (v - q θ t) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
  calc (T * cd) * wM t * |v^2 - (q θ t)^2|
      ≤ ((T * cd) * (5/59)) * ((15 + 143/10) * |v - q θ t|) := by
        apply mul_le_mul _ hp (abs_nonneg _)
          (mul_nonneg hTc (by norm_num))
        exact mul_le_mul_of_nonneg_left hw' hTc
    _ ≤ (9933/100000) * |v - q θ t| := by
        have hnn : (0:ℝ) ≤ |v - q θ t| := abs_nonneg _
        have hle : (2:ℝ) * (1/50) * (5/59) * (15 + 143/10) ≤ 9933/100000 := by
          norm_num
        simp only [T, cd]
        have heq : ((2:ℝ) * (1/50)) * (5/59) * ((15 + 143/10) * |v - q θ t|) =
            ((2:ℝ) * (1/50) * (5/59) * (15 + 143/10)) * |v - q θ t| := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right hle hnn

/-- Existence for the clipped drag field, from `BoundedODE`. -/
theorem exists_clipped (θ : ℝ) :
    ∃ v : ℝ → ℝ, Continuous v ∧ v 0 = 0 ∧
      ∀ t ∈ Icc 0 1, HasDerivAt v (field θ t (v t)) t :=
  BoundedODE.exists_time_dependent (fun t => field θ t)
    (⟨6/59, by norm_num⟩ : ℝ≥0) (⟨5429/100, by norm_num⟩ : ℝ≥0)
    (fun t => field_lipschitz θ t) (field_continuous θ)
    (fun t v => field_bound θ t v) 0 (by norm_num)

/-- The chosen solution of the clipped field. -/
def sol (θ : ℝ) : ℝ → ℝ := (exists_clipped θ).choose

theorem sol_continuous (θ : ℝ) : Continuous (sol θ) :=
  (exists_clipped θ).choose_spec.1
theorem sol_zero (θ : ℝ) : sol θ 0 = 0 :=
  (exists_clipped θ).choose_spec.2.1
theorem sol_deriv (θ : ℝ) :
    ∀ t ∈ Icc 0 1, HasDerivAt (sol θ) (field θ t (sol θ t)) t :=
  (exists_clipped θ).choose_spec.2.2

/-- The coarse upper ramp: drag only decelerates. -/
theorem sol_upper (θ : ℝ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    sol θ t ≤ (357/25) * t := by
  have hder : ∀ x ∈ uIcc 0 t, HasDerivAt (sol θ) (field θ x (sol θ x)) x :=
    by intro x hx; rw [uIcc_of_le ht.1] at hx; exact sol_deriv θ x ⟨hx.1, hx.2.trans ht.2⟩
  have hcont : ContinuousOn (fun x => field θ x (sol θ x)) (uIcc 0 t) :=
    ((field_continuous θ).comp (continuous_id.prodMk (sol_continuous θ))).continuousOn
  have hFTC : ∫ s in (0:ℝ)..t, field θ s (sol θ s) = sol θ t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hcont.intervalIntegrable,
      sol_zero, sub_zero]
  rw [← hFTC]
  have hint : ∫ s in (0:ℝ)..t, (357/25 : ℝ) = (357/25) * t := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring
  rw [← hint]
  apply intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht.1
    (hcont.intervalIntegrable)
    (intervalIntegrable_const)
  intro x hx
  exact field_le_upper θ x (sol θ x)

/-- The coarse lower ramp. -/
theorem sol_lower {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36))
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (1281/100 : ℝ) * t ≤ sol θ t := by
  have hder : ∀ x ∈ uIcc 0 t, HasDerivAt (sol θ) (field θ x (sol θ x)) x :=
    by intro x hx; rw [uIcc_of_le ht.1] at hx; exact sol_deriv θ x ⟨hx.1, hx.2.trans ht.2⟩
  have hcont : ContinuousOn (fun x => field θ x (sol θ x)) (uIcc 0 t) :=
    ((field_continuous θ).comp (continuous_id.prodMk (sol_continuous θ))).continuousOn
  have hFTC : ∫ s in (0:ℝ)..t, field θ s (sol θ s) = sol θ t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hcont.intervalIntegrable,
      sol_zero, sub_zero]
  rw [← hFTC]
  have hint : ∫ s in (0:ℝ)..t, (1281/100 : ℝ) = (1281/100) * t := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring
  rw [← hint]
  apply intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht.1
    (intervalIntegrable_const)
    (hcont.intervalIntegrable)
  intro x hx
  exact field_ge_lower hθ x (sol θ x)

/-- The clip is inactive along the solution. -/
theorem sol_mem {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36))
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : sol θ t ∈ Icc (0:ℝ) 15 := by
  constructor
  · have h := sol_lower hθ t ht
    have ht0 := ht.1
    linarith
  · have h := sol_upper θ t ht
    have ht1 := ht.2
    linarith

/-- Prediction error of the no-drag candidate. -/
def e (θ : ℝ) : ℝ → ℝ := fun t => sol θ t - q θ t
/-- Its derivative. -/
def de (θ : ℝ) : ℝ → ℝ := fun t => field θ t (sol θ t) - qd θ t

theorem wInt5_continuous : Continuous wInt5 := by
  show Continuous fun t : ℝ => (1/12)*t + (1/1440)*t^2 + (1/129600)*t^3 +
    (1/10368000)*t^4 + (1/777600000)*t^5 + (1/55987200000)*t^6
  continuity

theorem q_continuous (θ : ℝ) : Continuous (q θ) := by
  show Continuous fun t => T * (F * Real.cos θ * wInt5 t - g0 * t)
  exact continuous_const.mul (((continuous_const.mul continuous_const).mul
    wInt5_continuous).sub (continuous_const.mul continuous_id))

theorem e_continuous (θ : ℝ) : Continuous (e θ) := by
  show Continuous (fun t => sol θ t - q θ t)
  exact (sol_continuous θ).sub (q_continuous θ)

theorem e_hasDeriv (θ : ℝ) (t : ℝ) (ht : t ∈ Ico 0 1) :
    HasDerivAt (e θ) (de θ t) t := by
  show HasDerivAt (fun t => sol θ t - q θ t) (field θ t (sol θ t) - qd θ t) t
  exact (sol_deriv θ t ⟨ht.1, ht.2.le⟩).sub (q_hasDeriv θ t)

/-- The defect-plus-curvature bound along the solution. -/
theorem error_bound {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36))
    (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
    |de θ t| ≤ (9933/100000) * |e θ t| + 6932/10000 := by
  have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have hmem := sol_mem hθ t ht'
  have hq := q_bounds hθ t ht'
  have h1 := field_diff_bound (sol θ t) hmem t ht' hq
  have h2 := defect_bound hθ t ht'
  calc |de θ t| = |field θ t (sol θ t) - qd θ t| := rfl
    _ ≤ |field θ t (sol θ t) - field θ t (q θ t)| +
        |field θ t (q θ t) - qd θ t| := by
      rw [← sub_add_sub_cancel]; exact abs_add_le _ _
    _ ≤ (9933/100000) * |e θ t| + 6932/10000 := add_le_add h1 h2

/-- The exponential envelope and its derivative. -/
theorem envelope_hasDeriv (t : ℝ) :
    HasDerivAt (fun t => (69330/9933) * (Real.exp ((9933/100000) * t) - 1))
      ((6933/10000) * Real.exp ((9933/100000) * t)) t := by
  have h : HasDerivAt (fun s : ℝ => (9933/100000) * s) (9933/100000) t := by
    simpa using (hasDerivAt_id t).const_mul (9933/100000)
  have h2 := (Real.hasDerivAt_exp ((9933/100000) * t)).comp t h
  have h3 := (h2.sub_const 1).const_mul (69330/9933)
  refine h3.congr_deriv ?_
  have hC : (69330/9933 : ℝ) * (9933/100000) = 6933/10000 := by norm_num
  calc (69330/9933 : ℝ) * (Real.exp ((9933/100000) * t) * (9933/100000))
      = ((69330/9933) * (9933/100000)) * Real.exp ((9933/100000) * t) := by ring
    _ = (6933/10000) * Real.exp ((9933/100000) * t) := by rw [hC]

/-- The drag certificate: neglecting quadratic drag on the 2 s ascent costs
at most this envelope, for every tilt in the family. -/
theorem drag_certificate {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36))
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    |e θ t| ≤ (69330/9933) * (Real.exp ((9933/100000) * t) - 1) := by
  have h := FirstOrderCertificate.certificate_boundary (e θ) (de θ)
    (fun t => (69330/9933) * (Real.exp ((9933/100000) * t) - 1))
    (fun t => (6933/10000) * Real.exp ((9933/100000) * t))
    (e_continuous θ) (fun s hs => e_hasDeriv θ s hs) envelope_hasDeriv
    (by simp [e, sol_zero, q_zero, Real.exp_zero]) (by
      intro s hs hbs
      have h1 := error_bound hθ s hs
      rw [Real.norm_eq_abs] at hbs
      rw [hbs] at h1
      rw [Real.norm_eq_abs]
      refine h1.trans_lt ?_
      have hexp : 0 < Real.exp ((9933/100000) * s) := Real.exp_pos _
      have hC : (9933/100000 : ℝ) * ((69330/9933) *
          (Real.exp ((9933/100000) * s) - 1)) =
          (6933/10000) * (Real.exp ((9933/100000) * s) - 1) := by
        rw [← mul_assoc]
        rw [show (9933/100000 : ℝ) * (69330/9933) = 6933/10000 by norm_num]
      rw [hC]
      nlinarith [hexp])
  have h' := h t ht
  rw [Real.norm_eq_abs] at h'
  exact h'

/-- The exponential bound e^x ≤ (1-x)⁻¹ for x < 1. -/
theorem exp_le_inv_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ (1 - x)⁻¹ := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  rw [Real.exp_neg] at h1
  have h2 : (0:ℝ) < 1 - x := by linarith
  have h3 : (0:ℝ) < Real.exp x := Real.exp_pos x
  have h4 : ((Real.exp x)⁻¹)⁻¹ ≤ (1 - x)⁻¹ := inv_anti₀ (by positivity) h1
  rwa [inv_inv] at h4

/-- The endpoint value: at most 0.7698 m/s. -/
theorem drag_endpoint {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi/36)) (Real.pi/36)) :
    |e θ 1| ≤ 7698/10000 := by
  have h := drag_certificate hθ 1 ⟨by norm_num, le_rfl⟩
  refine h.trans ?_
  have hexp := exp_le_inv_sub (x := (9933/100000)) (by norm_num)
  have h1 : (1 - (9933/100000 : ℝ))⁻¹ - 1 = (9933/100000)/(90067/100000) := by
    rw [inv_eq_one_div]; field_simp; norm_num
  have h2 : Real.exp ((9933/100000) * 1) - 1 ≤ (9933/100000)/(90067/100000) := by
    rw [mul_one]
    linarith [hexp, h1]
  calc (69330/9933) * (Real.exp ((9933/100000) * 1) - 1)
      ≤ (69330/9933) * ((9933/100000)/(90067/100000)) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ 7698/10000 := by norm_num

end GNC.DragCertificate
