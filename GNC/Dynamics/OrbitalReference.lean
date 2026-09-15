import GNC.Dynamics.OrbitalBarrier
import GNC.Dynamics.Atmosphere
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Sampling-free reference envelopes using orbital invariants.
The eccentricity (Laplace--Runge--Lenz) vector retains the correlation
between energy and angular momentum that separate scalar budgets lose.
The following formulas are valid in a real inner product space and do not
assume an exactly Keplerian trajectory when noncentral acceleration is present.
-/
noncomputable section
open Set Real
open scoped RealInnerProductSpace
namespace GNC.OrbitalReference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def eccentricityVector (mu : ℝ) (p v : E) : E :=
  (‖v‖^2-mu/‖p‖) • p-⟪p,v⟫ • v

def eccentricityRate (p v a : E) : E :=
  (2*⟪v,a⟫) • p-⟪p,a⟫ • v-⟪p,v⟫ • a

theorem eccentricity_derivative {p v : ℝ → E} {mu t : ℝ} {a : E}
    (hp : HasDerivAt p (v t) t)
    (hv : HasDerivAt v (Gravity.field mu (p t)+a) t) (hz : p t ≠ 0) :
    HasDerivAt (fun s => eccentricityVector mu (p s) (v s))
      (eccentricityRate (p t) (v t) a) t := by
  have hn : ‖p t‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  convert (((hv.norm_sq).sub ((hasDerivAt_const t mu).div
    (Gravity.norm_derivative hp hz) hn)).smul hp).sub ((hp.inner ℝ hv).smul hv) using 1
  simp only [eccentricityRate, Gravity.field, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm (v t) (p t)]
  dsimp only [Pi.sub_apply, Pi.div_apply]
  match_scalars <;> field_simp <;> ring

theorem eccentricity_rate_bound (p v a : E) :
    ‖eccentricityRate p v a‖ ≤ 4*‖p‖*‖v‖*‖a‖ := by
  have h₁ := abs_real_inner_le_norm v a
  have h₂ := abs_real_inner_le_norm p a
  have h₃ := abs_real_inner_le_norm p v
  have ht := (norm_sub_le ((2*⟪v,a⟫) • p-⟪p,a⟫ • v) (⟪p,v⟫ • a)).trans
    (add_le_add_left (norm_sub_le ((2*⟪v,a⟫) • p) (⟪p,a⟫ • v)) _)
  norm_num only [norm_smul, Real.norm_eq_abs, abs_mul] at ht
  have ha := mul_le_mul_of_nonneg_right h₁ (norm_nonneg p)
  have hb := mul_le_mul_of_nonneg_right h₂ (norm_nonneg v)
  have hc := mul_le_mul_of_nonneg_right h₃ (norm_nonneg a)
  dsimp [eccentricityRate]
  nlinarith

/-- The eccentricity-vector radial identity, with no Kepler approximation. -/
theorem radial_identity (mu : ℝ) (p v : E) (hz : p ≠ 0) :
    ⟪eccentricityVector mu p v,p⟫ = OrbitalBarrier.momentumSq p v-mu*‖p‖ := by
  have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp only [eccentricityVector, OrbitalBarrier.momentumSq, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm v p]
  field_simp
  ring

/-- Absolute momentum and eccentricity changes on a prefix. -/
theorem invariant_changes (p v a : ℝ → E) {mu T R V D : ℝ}
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hV : 0 ≤ V) (hD : 0 ≤ D)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (Gravity.field mu (p t)+a t) t)
    (hz : ∀ t ∈ Icc 0 T, p t ≠ 0)
    (hr : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ R)
    (hs : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ V)
    (ha : ∀ t ∈ Icc 0 T, ‖a t‖ ≤ D) :
    |OrbitalBarrier.momentumSq (p T) (v T)-OrbitalBarrier.momentumSq (p 0) (v 0)|
      ≤ 4*R^2*V*D*T ∧
    ‖eccentricityVector mu (p T) (v T)‖
      ≤ ‖eccentricityVector mu (p 0) (v 0)‖+4*R*V*D*T := by
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (OrbitalBarrier.momentum_derivative (hp t ht) (hv t ht)).hasDerivWithinAt)
    (fun t ht => show ‖OrbitalBarrier.momentumRate (p t) (v t) (a t)‖ ≤ 4*R^2*V*D from by
      have ht' := Ico_subset_Icc_self ht
      have hsq : ‖p t‖^2 ≤ R^2 := by nlinarith [norm_nonneg (p t), hr t ht']
      exact (OrbitalBarrier.momentum_rate_bound (p t) (v t) (a t)).trans
        (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num))
          (hs t ht') (norm_nonneg _) (by positivity))
          (ha t ht') (norm_nonneg _) (by positivity))) T (right_mem_Icc.mpr hT)
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (eccentricity_derivative (hp t ht) (hv t ht) (hz t ht)).hasDerivWithinAt)
    (fun t ht => (eccentricity_rate_bound (p t) (v t) (a t)).trans (by
      have ht' := Ico_subset_Icc_self ht
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (hr t ht') (by norm_num))
        (hs t ht') (norm_nonneg _) (by positivity)) (ha t ht') (norm_nonneg _) (by positivity)))
    T (right_mem_Icc.mpr hT)
  simp only [Real.norm_eq_abs, sub_zero] at hm he
  have hnorm := norm_sub_norm_le (eccentricityVector mu (p T) (v T)) (eccentricityVector mu (p 0) (v 0))
  exact ⟨hm, by linarith⟩

/-- A noncircular annulus proof retaining eccentricity-vector information.
The noncentral force bound is required only while the trajectory is inside
this annulus. The conclusion establishes the regional hypotheses on every
real time in the horizon, independently of any numerical orbit. -/
theorem annulus (p v a : ℝ → E) {mu T lo hi V D energy hminus hplus ecc : ℝ}
    (hmu : 0 ≤ mu) (hT : 0 ≤ T) (hlo : 0 < lo) (hgap : lo < hi)
    (hV : 0 < V) (hD : 0 ≤ D) (hpcont : Continuous p) (hvcont : Continuous v)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (Gravity.field mu (p t)+a t) t)
    (hforce : ∀ t ∈ Icc 0 T,
      lo ≤ ‖p t‖ → ‖p t‖ ≤ hi → ‖v t‖ ≤ V → ‖a t‖ ≤ D)
    (hinit : lo < ‖p 0‖ ∧ ‖p 0‖ < hi ∧ ‖v 0‖ < V)
    (he : OrbitalEnergy.specificEnergy mu (p 0) (v 0)+V*D*T ≤ energy)
    (hm : hminus ≤ OrbitalBarrier.momentumSq (p 0) (v 0)-4*hi^2*V*D*T)
    (hM : OrbitalBarrier.momentumSq (p 0) (v 0)+4*hi^2*V*D*T ≤ hplus)
    (hee : ‖eccentricityVector mu (p 0) (v 0)‖+4*hi*V*D*T ≤ ecc)
    (hlow : (mu+ecc)*lo < hminus)
    (hhigh : hplus < (mu-ecc)*hi)
    (hspeed : 2*(energy+mu/lo) < V^2) :
    ∀ t ∈ Icc 0 T, lo < ‖p t‖ ∧ ‖p t‖ < hi ∧ ‖v t‖ < V := by
  have hhi : 0 < hi := hlo.trans hgap
  have hg : Continuous (fun t => OrbitalBarrier.guard lo hi V (p t) (v t)) := by
    unfold OrbitalBarrier.guard
    fun_prop
  have h := IntegralTube.prefix_closure hg
    ((OrbitalBarrier.guard_lt_iff (p 0) (v 0) hgap hV).mpr hinit)
    (a := 0) (b := T) (fun t ht hprefix => by
      have hb s (hs : s ∈ Icc 0 t) :=
        (OrbitalBarrier.guard_le_iff (p s) (v s) hgap hV).mp (hprefix s hs)
      have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
      have hz s (hs : s ∈ Icc 0 t) : p s ≠ 0 :=
        norm_pos_iff.mp (hlo.trans_le (hb s hs).1)
      have hf s (hs : s ∈ Icc 0 t) :=
        hforce s (hsub hs) (hb s hs).1 (hb s hs).2.1 (hb s hs).2.2
      have budgets := OrbitalBarrier.invariant_budgets p v a ht.1 (hlo.le.trans hgap.le) hV.le hD
        (fun s hs => hp s (hsub hs)) (fun s hs => hv s (hsub hs)) hz
        (fun s hs => (hb s hs).2.1) (fun s hs => (hb s hs).2.2) hf
      have changes := invariant_changes p v a ht.1 (hlo.le.trans hgap.le) hV.le hD
        (fun s hs => hp s (hsub hs)) (fun s hs => hv s (hsub hs)) hz
        (fun s hs => (hb s hs).2.1) (fun s hs => (hb s hs).2.2) hf
      have henergy : OrbitalEnergy.specificEnergy mu (p t) (v t) ≤ energy := by
        have htime := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hV.le hD)
        linarith [budgets.1]
      have hmomentum : hminus ≤ OrbitalBarrier.momentumSq (p t) (v t) ∧
          OrbitalBarrier.momentumSq (p t) (v t) ≤ hplus := by
        have htime := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 4*hi^2*V*D by positivity)
        constructor <;> linarith [(abs_le.mp changes.1).1, (abs_le.mp changes.1).2]
      have hecc : ‖eccentricityVector mu (p t) (v t)‖ ≤ ecc := by
        have htime := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 4*hi*V*D by positivity)
        linarith [changes.2]
      have hrad := abs_real_inner_le_norm (eccentricityVector mu (p t) (v t)) (p t)
      rw [radial_identity mu (p t) (v t) (hz t (right_mem_Icc.mpr ht.1))] at hrad
      have hbound := mul_le_mul_of_nonneg_right hecc (norm_nonneg (p t))
      have hlower := (abs_le.mp hrad).1
      have hupper := (abs_le.mp hrad).2
      have hnow := hb t (right_mem_Icc.mpr ht.1)
      have hl : lo < ‖p t‖ := by
        by_contra hh
        have heq : ‖p t‖ = lo := by linarith [hnow.1]
        rw [heq] at hlower hupper hbound
        nlinarith [hmomentum.1]
      have hu : ‖p t‖ < hi := by
        by_contra hh
        have heq : ‖p t‖ = hi := by linarith [hnow.2.1]
        rw [heq] at hlower hupper hbound
        nlinarith [hmomentum.2]
      have hs : ‖v t‖ < V := by
        have hrecip := div_le_div_of_nonneg_left hmu hlo hnow.1
        dsimp [OrbitalEnergy.specificEnergy] at henergy
        nlinarith [norm_nonneg (v t)]
      exact (OrbitalBarrier.guard_lt_iff (p t) (v t) hgap hV).mpr ⟨hl,hu,hs⟩)
  intro t ht
  exact (OrbitalBarrier.guard_lt_iff (p t) (v t) hgap hV).mp (h t ht)


/-- Normalized Kepler periapsis data used by both mission initializers. -/
theorem periapsis_invariants (p v : E) {e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hr : ‖p‖ = 1-e) (hv : ‖v‖^2 = (1+e)/(1-e)) (ho : ⟪p,v⟫ = 0) :
    OrbitalEnergy.specificEnergy 1 p v = -1/2 ∧
    OrbitalBarrier.momentumSq p v = 1-e^2 ∧
    ‖eccentricityVector 1 p v‖ = e := by
  have hd : 0 < 1-e := sub_pos.mpr he1
  constructor
  · dsimp [OrbitalEnergy.specificEnergy]
    rw [hr, hv]
    field_simp
    ring
  constructor
  · dsimp [OrbitalBarrier.momentumSq]
    rw [hr, hv, ho]
    field_simp
    ring
  · dsimp [eccentricityVector]
    rw [hv, hr, ho, zero_smul, sub_zero, ← sub_div, add_sub_cancel_left]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg he hd.le), hr]
    exact div_mul_cancel₀ e hd.ne'

/-- Physical noncentral acceleration: exponential-density quadratic drag and
an arbitrary thrust direction with norm at most one. -/
def noncentral (coefficient H r₀ thrust : ℝ) (p v wind direction : E) : E :=
  -(coefficient*Atmosphere.density H r₀ p) • QuadraticDrag.field (v-wind)+thrust • direction

theorem noncentral_bound (coefficient H r₀ thrust : ℝ) (p v wind direction : E)
    {C W : ℝ} (hc : |coefficient*Atmosphere.density H r₀ p| ≤ C)
    (hw : ‖v-wind‖ ≤ W) (hd : ‖direction‖ ≤ 1) :
    ‖noncentral coefficient H r₀ thrust p v wind direction‖ ≤ C*W^2+|thrust| := by
  have hC : 0 ≤ C := (abs_nonneg _).trans hc
  have hW : 0 ≤ W := (norm_nonneg _).trans hw
  have hsq : ‖v-wind‖^2 ≤ W^2 := by nlinarith [norm_nonneg (v-wind)]
  have h := norm_add_le (-(coefficient*Atmosphere.density H r₀ p) • QuadraticDrag.field (v-wind))
    (thrust • direction)
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, QuadraticDrag.field_norm] at h
  exact h.trans (by nlinarith [mul_le_mul hc hsq (sq_nonneg _) hC,
    mul_le_mul_of_nonneg_left hd (abs_nonneg thrust)])

theorem relative_wind_bound (p v wind : E) {R V spin : ℝ}
    (hspin : 0 ≤ spin) (hr : ‖p‖ ≤ R) (hv : ‖v‖ ≤ V)
    (hw : ‖wind‖ ≤ spin*‖p‖) : ‖v-wind‖ ≤ V+spin*R :=
  (norm_sub_le v wind).trans (add_le_add hv
    (hw.trans (mul_le_mul_of_nonneg_left hr hspin)))


/-- Retaining the eccentricity vector gives a radius error linear in small
invariant budgets near a circular reference (mu = nominal radius = 1). -/
theorem radius_deviation (p v : E) {delta ecc : ℝ} (hz : p ≠ 0)
    (hdelta : 0 ≤ delta) (hecc : 0 ≤ ecc) (hecc1 : ecc < 1)
    (hm : |OrbitalBarrier.momentumSq p v-1| ≤ delta)
    (he : ‖eccentricityVector 1 p v‖ ≤ ecc) :
    |‖p‖-1| ≤ (delta+ecc)/(1-ecc) := by
  have h := (abs_real_inner_le_norm (eccentricityVector 1 p v) p).trans
    (mul_le_mul_of_nonneg_right he (norm_nonneg p))
  rw [radial_identity 1 p v hz, one_mul] at h
  have hb := abs_le.mp h
  have hm' := abs_le.mp hm
  have hden : 0 < 1-ecc := sub_pos.mpr hecc1
  apply abs_le.mpr
  constructor
  · have hl : 1-‖p‖ ≤ (delta+ecc)/(1-ecc) := by
      apply (le_div_iff₀ hden).mpr
      by_cases hr : 1 ≤ ‖p‖
      · have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hden.le
        linarith
      · have hh := mul_nonneg hecc (show 0 ≤ 1-‖p‖ by linarith)
        nlinarith [hb.2, hm'.1]
    linarith
  · apply (le_div_iff₀ hden).mpr
    nlinarith [hb.1, hm'.2]

end GNC.OrbitalReference
