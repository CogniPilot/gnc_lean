import GNC.Dynamics.OrbitalEnergy
import GNC.Control.IntegralTube
import Mathlib.Analysis.Calculus.MeanValue

/-! Continuous orbital annulus certificates from energy and angular momentum.
The force bound is required only inside the proposed annulus. A first-exit
argument discharges that regional hypothesis without sampling a trajectory.
All norms are Hilbert-space norms; in three dimensions `momentumSq` is the
squared physical angular-momentum norm. -/
noncomputable section
open Set Real
open scoped RealInnerProductSpace
namespace GNC.OrbitalBarrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def momentumSq (p v : E) : ℝ := ‖p‖^2*‖v‖^2-⟪p,v⟫^2

def momentumRate (p v a : E) : ℝ :=
  2*(‖p‖^2*⟪v,a⟫-⟪p,v⟫*⟪p,a⟫)

theorem momentum_derivative {p v : ℝ → E} {mu t : ℝ} {a : E}
    (hp : HasDerivAt p (v t) t)
    (hv : HasDerivAt v (Gravity.field mu (p t)+a) t) :
    HasDerivAt (fun s => momentumSq (p s) (v s)) (momentumRate (p t) (v t) a) t := by
  convert (hp.norm_sq.mul hv.norm_sq).sub ((hp.inner ℝ hv).pow 2) using 1
  simp only [momentumRate, Gravity.field, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm (v t) (p t)]
  ring

theorem momentum_rate_bound (p v a : E) :
    |momentumRate p v a| ≤ 4*‖p‖^2*‖v‖*‖a‖ := by
  have h₁ : |‖p‖^2*⟪v,a⟫| ≤ ‖p‖^2*(‖v‖*‖a‖) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm v a) (sq_nonneg _)
  have h₂ : |⟪p,v⟫*⟪p,a⟫| ≤ (‖p‖*‖v‖)*(‖p‖*‖a‖) := by
    rw [abs_mul]
    exact mul_le_mul (abs_real_inner_le_norm p v) (abs_real_inner_le_norm p a)
      (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  dsimp [momentumRate]
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h := abs_sub (‖p‖^2*⟪v,a⟫) (⟪p,v⟫*⟪p,a⟫)
  nlinarith

theorem radial_constraint (p v : E) {mu energy lower : ℝ}
    (hp : p ≠ 0) (he : OrbitalEnergy.specificEnergy mu p v ≤ energy)
    (hh : lower ≤ momentumSq p v) :
    0 ≤ 2*energy*‖p‖^2+2*mu*‖p‖-lower := by
  have hr : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have h := mul_le_mul_of_nonneg_right he (sq_nonneg ‖p‖)
  have hid : OrbitalEnergy.specificEnergy mu p v*‖p‖^2 =
      ‖p‖^2*‖v‖^2/2-mu*‖p‖ := by
    dsimp [OrbitalEnergy.specificEnergy]
    field_simp
  rw [hid] at h
  dsimp [momentumSq] at hh
  nlinarith [sq_nonneg ⟪p,v⟫]

/-- Prefix energy and squared-momentum budgets from actual derivatives.
The bound on noncentral acceleration is uniform over this entire prefix. -/
theorem invariant_budgets (p v a : ℝ → E) {mu T R V D : ℝ}
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hV : 0 ≤ V) (hD : 0 ≤ D)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (Gravity.field mu (p t)+a t) t)
    (hz : ∀ t ∈ Icc 0 T, p t ≠ 0)
    (hr : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ R)
    (hs : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ V)
    (ha : ∀ t ∈ Icc 0 T, ‖a t‖ ≤ D) :
    OrbitalEnergy.specificEnergy mu (p T) (v T) ≤
      OrbitalEnergy.specificEnergy mu (p 0) (v 0)+V*D*T ∧
    momentumSq (p 0) (v 0)-4*R^2*V*D*T ≤ momentumSq (p T) (v T) := by
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (OrbitalEnergy.energy_derivative (hp t ht) (hv t ht) (hz t ht)).hasDerivWithinAt)
    (fun t ht => (abs_real_inner_le_norm (v t) (a t)).trans
      (mul_le_mul (hs t (Ico_subset_Icc_self ht)) (ha t (Ico_subset_Icc_self ht))
        (norm_nonneg _) hV)) T (right_mem_Icc.mpr hT)
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (momentum_derivative (hp t ht) (hv t ht)).hasDerivWithinAt)
    (fun t ht => show ‖momentumRate (p t) (v t) (a t)‖ ≤ 4*R^2*V*D from by
      have ht' := Ico_subset_Icc_self ht
      have hsq : ‖p t‖^2 ≤ R^2 := by nlinarith [norm_nonneg (p t), hr t ht']
      exact (momentum_rate_bound (p t) (v t) (a t)).trans
        (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num))
          (hs t ht') (norm_nonneg _) (by positivity))
          (ha t ht') (norm_nonneg _) (by positivity))) T (right_mem_Icc.mpr hT)
  simp only [Real.norm_eq_abs, sub_zero] at he hm
  constructor
  · linarith [(abs_le.mp he).2]
  · linarith [(abs_le.mp hm).1]

def guard (lower upper speed : ℝ) (p v : E) : ℝ :=
  max ((lower+upper-2*‖p‖)/(upper-lower))
    (max ((2*‖p‖-lower-upper)/(upper-lower)) (‖v‖/speed))

theorem guard_le_iff (p v : E) {lo hi V : ℝ} (hgap : lo < hi) (hV : 0 < V) :
    guard lo hi V p v ≤ 1 ↔ lo ≤ ‖p‖ ∧ ‖p‖ ≤ hi ∧ ‖v‖ ≤ V := by
  simp only [guard, max_le_iff, div_le_one (sub_pos.mpr hgap), div_le_one hV]
  constructor <;> intro h <;> rcases h with ⟨h₁, h₂, h₃⟩ <;> constructor <;> try linarith
  all_goals constructor <;> linarith

theorem guard_lt_iff (p v : E) {lo hi V : ℝ} (hgap : lo < hi) (hV : 0 < V) :
    guard lo hi V p v < 1 ↔ lo < ‖p‖ ∧ ‖p‖ < hi ∧ ‖v‖ < V := by
  simp only [guard, max_lt_iff, div_lt_one (sub_pos.mpr hgap), div_lt_one hV]
  constructor <;> intro h <;> rcases h with ⟨h₁, h₂, h₃⟩ <;> constructor <;> try linarith
  all_goals constructor <;> linarith

/-- A continuous-time annulus certificate, independent of a numerical orbit.
The three strict scalar inequalities are checkable with rational arithmetic.
Only the noncentral force bound is regional; the conclusion proves that the
actual trajectory stays in that region throughout the entire horizon. -/
theorem annulus (p v a : ℝ → E) {mu T lo hi V D energy momentum : ℝ}
    (hmu : 0 ≤ mu) (hT : 0 ≤ T) (hlo : 0 < lo) (hgap : lo < hi)
    (hV : 0 < V) (hD : 0 ≤ D) (hpcont : Continuous p) (hvcont : Continuous v)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (Gravity.field mu (p t)+a t) t)
    (hforce : ∀ t ∈ Icc 0 T,
      lo ≤ ‖p t‖ → ‖p t‖ ≤ hi → ‖v t‖ ≤ V → ‖a t‖ ≤ D)
    (hinit : lo < ‖p 0‖ ∧ ‖p 0‖ < hi ∧ ‖v 0‖ < V)
    (he : OrbitalEnergy.specificEnergy mu (p 0) (v 0)+V*D*T ≤ energy)
    (hm : momentum ≤ momentumSq (p 0) (v 0)-4*hi^2*V*D*T)
    (hlow : 2*energy*lo^2+2*mu*lo-momentum < 0)
    (hhigh : 2*energy*hi^2+2*mu*hi-momentum < 0)
    (hspeed : 2*(energy+mu/lo) < V^2) :
    ∀ t ∈ Icc 0 T, lo < ‖p t‖ ∧ ‖p t‖ < hi ∧ ‖v t‖ < V := by
  have hg : Continuous (fun t => guard lo hi V (p t) (v t)) := by
    unfold guard
    fun_prop
  have h := IntegralTube.prefix_closure hg ((guard_lt_iff (p 0) (v 0) hgap hV).mpr hinit)
    (a := 0) (b := T) (fun t ht hprefix => by
      have hb s (hs : s ∈ Icc 0 t) :=
        (guard_le_iff (p s) (v s) hgap hV).mp (hprefix s hs)
      have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
      have hz s (hs : s ∈ Icc 0 t) : p s ≠ 0 :=
        norm_pos_iff.mp (hlo.trans_le (hb s hs).1)
      have budgets := invariant_budgets p v a ht.1 (hlo.le.trans hgap.le) hV.le hD
        (fun s hs => hp s (hsub hs)) (fun s hs => hv s (hsub hs)) hz
        (fun s hs => (hb s hs).2.1) (fun s hs => (hb s hs).2.2)
        (fun s hs => hforce s (hsub hs) (hb s hs).1 (hb s hs).2.1 (hb s hs).2.2)
      have henergy : OrbitalEnergy.specificEnergy mu (p t) (v t) ≤ energy := by
        have htime := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hV.le hD)
        linarith [budgets.1]
      have hmomentum : momentum ≤ momentumSq (p t) (v t) := by
        have htime := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 4*hi^2*V*D by positivity)
        linarith [budgets.2]
      have hrad := radial_constraint (p t) (v t) (hz t (right_mem_Icc.mpr ht.1)) henergy hmomentum
      have hnow := hb t (right_mem_Icc.mpr ht.1)
      have hl : lo < ‖p t‖ := by
        by_contra hh
        have heq : ‖p t‖ = lo := by linarith [hnow.1]
        rw [heq] at hrad
        linarith
      have hu : ‖p t‖ < hi := by
        by_contra hh
        have heq : ‖p t‖ = hi := by linarith [hnow.2.1]
        rw [heq] at hrad
        linarith
      have hs : ‖v t‖ < V := by
        have hrecip := div_le_div_of_nonneg_left hmu hlo hnow.1
        dsimp [OrbitalEnergy.specificEnergy] at henergy
        nlinarith [norm_nonneg (v t)]
      exact (guard_lt_iff (p t) (v t) hgap hV).mpr ⟨hl,hu,hs⟩)
  intro t ht
  exact (guard_lt_iff (p t) (v t) hgap hV).mp (h t ht)

end GNC.OrbitalBarrier
