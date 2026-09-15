import GNC.Analysis.PolynomialLieSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecificLimits.Basic

/-! Explicit factorial majorants for all Lie derivatives of a polynomial
field on the unit coordinate cube. Constants are computed from the field's
degree and absolute coefficient bound, rather than numerical tolerances.
-/
namespace GNC.PolynomialODE.Expr
open scoped ContDiff
variable {n : ℕ}

def degree : Expr n → ℕ
  | .constant _ => 0
  | .var _ => 1
  | .add a b => max a.degree b.degree
  | .multiply a b => a.degree+b.degree
  | .negate a => a.degree

def fieldMajorant (f : Fin n → Expr n) : ℚ := ∑ i, (f i).majorant 1
def fieldDegree (f : Fin n → Expr n) : ℕ := max 1 (∑ i, (f i).degree)

theorem fieldMajorant_nonneg (f : Fin n → Expr n) : 0 ≤ fieldMajorant f :=
  Finset.sum_nonneg (fun i _ => (f i).majorant_nonneg (by norm_num))

theorem le_fieldMajorant (f : Fin n → Expr n) (i : Fin n) :
    (f i).majorant 1 ≤ fieldMajorant f :=
  Finset.single_le_sum (fun j _ => (f j).majorant_nonneg (by norm_num)) (Finset.mem_univ i)

theorem fieldDegree_pos (f : Fin n → Expr n) : 1 ≤ fieldDegree f := le_max_left _ _

theorem le_fieldDegree (f : Fin n → Expr n) (i : Fin n) :
    (f i).degree ≤ fieldDegree f := by
  have h : (f i).degree ≤ ∑ j, (f j).degree :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((f j).degree)) (Finset.mem_univ i)
  exact h.trans (le_max_right _ _)

theorem lieDerivative_degree (f : Fin n → Expr n) (e : Expr n) {d : ℕ}
    (hf : ∀ i, (f i).degree ≤ d) :
    (lieDerivative f e).degree ≤ e.degree+d := by
  induction e with
  | constant c => simp [lieDerivative, degree]
  | var i => simpa [lieDerivative, degree] using (hf i).trans (Nat.le_add_left d 1)
  | add a b ha hb =>
    simp only [lieDerivative, degree]
    omega
  | multiply a b ha hb =>
    simp only [lieDerivative, degree]
    omega
  | negate a ha => exact ha

theorem slope_degree (e : Expr n) : e.slope 1 ≤ (e.degree:ℚ)*e.majorant 1 := by
  induction e with
  | constant c => simp [slope, degree]
  | var i => simp [slope, degree, majorant]
  | add a b ha hb =>
    have hma := a.majorant_nonneg (by norm_num : (0:ℚ) ≤ 1)
    have hmb := b.majorant_nonneg (by norm_num : (0:ℚ) ≤ 1)
    have hda : (a.degree:ℚ) ≤ max a.degree b.degree := by exact_mod_cast le_max_left _ _
    have hdb : (b.degree:ℚ) ≤ max a.degree b.degree := by exact_mod_cast le_max_right _ _
    simp only [slope, degree, majorant]
    nlinarith
  | multiply a b ha hb =>
    have hma := a.majorant_nonneg (by norm_num : (0:ℚ) ≤ 1)
    have hmb := b.majorant_nonneg (by norm_num : (0:ℚ) ≤ 1)
    simp only [slope, degree, majorant, Nat.cast_add]
    nlinarith [mul_le_mul_of_nonneg_left ha hmb, mul_le_mul_of_nonneg_left hb hma]
  | negate a ha => exact ha

theorem lieDerivative_majorant (f : Fin n → Expr n) (e : Expr n) {C : ℚ}
    (hC : 0 ≤ C) (hf : ∀ i, (f i).majorant 1 ≤ C) :
    (lieDerivative f e).majorant 1 ≤ C*e.slope 1 := by
  induction e with
  | constant c => simp [lieDerivative, majorant, slope]
  | var i => simpa [lieDerivative, majorant, slope] using hf i
  | add a b ha hb => simp only [lieDerivative, majorant, slope]; linarith
  | multiply a b ha hb =>
    have hma := a.majorant_nonneg (by norm_num : (0:ℚ) ≤ 1)
    have hmb := b.majorant_nonneg (by norm_num : (0:ℚ) ≤ 1)
    simp only [lieDerivative, majorant, slope]
    nlinarith [mul_le_mul_of_nonneg_right ha hmb, mul_le_mul_of_nonneg_left hb hma]
  | negate a ha => exact ha

theorem lieIterate_degree (f : Fin n → Expr n) {d : ℕ}
    (hf : ∀ i, (f i).degree ≤ d) (k : ℕ) (i : Fin n) :
    (lieIterate f k (.var i)).degree ≤ 1+k*d := by
  induction k with
  | zero => simp [lieIterate, degree]
  | succ k ih =>
    have h := lieDerivative_degree f (lieIterate f k (.var i)) hf
    simp only [lieIterate] at *
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- A single field bound and degree bound control all derivative orders. -/
theorem lieIterate_factorial (f : Fin n → Expr n) {C : ℚ} {d : ℕ}
    (hC : 0 ≤ C) (hd : 1 ≤ d)
    (hfC : ∀ i, (f i).majorant 1 ≤ C) (hfd : ∀ i, (f i).degree ≤ d)
    (k : ℕ) (i : Fin n) :
    (lieIterate f k (.var i)).majorant 1 ≤ (C*d)^k*(k.factorial:ℚ) := by
  induction k with
  | zero => simp [lieIterate, majorant]
  | succ k ih =>
    have hg := lieIterate_degree f hfd k i
    have hg' : ((lieIterate f k (.var i)).degree:ℚ) ≤ (d:ℚ)*(k+1) := by
      exact_mod_cast (show (lieIterate f k (.var i)).degree ≤ d*(k+1) by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm d k]
        omega)
    have hm := (lieIterate f k (.var i)).majorant_nonneg (by norm_num : (0:ℚ) ≤ 1)
    calc
      _ ≤ C*(lieIterate f k (.var i)).slope 1 :=
        lieDerivative_majorant f _ hC hfC
      _ ≤ C*(((lieIterate f k (.var i)).degree:ℚ)*
          (lieIterate f k (.var i)).majorant 1) :=
        mul_le_mul_of_nonneg_left (slope_degree _) hC
      _ ≤ C*((d:ℚ)*(k+1)*(lieIterate f k (.var i)).majorant 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg' hm) hC
      _ ≤ C*((d:ℚ)*(k+1)*((C*d)^k*(k.factorial:ℚ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ih (by positivity)) hC
      _ = (C*d)^(k+1)*((k+1).factorial:ℚ) := by
        rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring

theorem value_contDiff (e : Expr n) : ContDiff ℝ ∞ e.value := by
  induction e with
  | constant c => exact contDiff_const
  | var i => exact contDiff_apply ℝ ℝ i
  | add a b ha hb => exact ha.add hb
  | multiply a b ha hb => exact ha.mul hb
  | negate a ha => exact ha.neg

noncomputable def partialFlow (f : Fin n → Expr n) (z₀ : Fin n → ℝ)
    (N : ℕ) (t : ℝ) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.range (N+1), ((k.factorial:ℝ)⁻¹*t^k)*
    (lieIterate f k (.var i)).value z₀

open Set Filter
open scoped Topology

/-- The exact physical remainder, with a field-derived bound at every
order. The smooth solution may be restricted to any open time interval;
the unit cube condition is on the actual solution over this one step. -/
theorem partialFlow_error (f : Fin n → Expr n) {C : ℚ} {d : ℕ}
    (hC : 0 ≤ C) (hd : 1 ≤ d)
    (hfC : ∀ i, (f i).majorant 1 ≤ C) (hfd : ∀ i, (f i).degree ≤ d)
    {z : ℝ → Fin n → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hz : ∀ t ∈ S, HasDerivAt z (fun i => (f i).value (z t)) t)
    (hsmooth : ContDiffOn ℝ ∞ z S) {T : ℝ} (hT : 0 < T)
    (hstep : Icc 0 T ⊆ S) (hregion : ∀ t ∈ Icc 0 T, ∀ i, |z t i| ≤ 1)
    (N : ℕ) (i : Fin n) :
    |z T i-partialFlow f (z 0) N T i| ≤ ((C:ℝ)*d*T)^(N+1) := by
  let F : ℝ → ℝ := fun s => z s i
  have hF : ContDiffOn ℝ ∞ F S :=
    (value_contDiff (.var i)).comp_contDiffOn hsmooth
  have hpoly : taylorWithinEval F N (Icc 0 T) 0 T = partialFlow f (z 0) N T i := by
    rw [taylor_within_apply]
    unfold partialFlow
    apply Finset.sum_congr rfl
    intro k hk
    have hc := hF.contDiffAt (hS.mem_nhds (hstep ⟨le_rfl,hT.le⟩))
    have horder : (k:WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT)
      (hc.of_le horder) (by simp [hT.le])]
    rw [show iteratedDeriv k F 0 = (lieIterate f k (.var i)).value (z 0) from
      lieIterate_derivative f (.var i) hS hz k (hstep ⟨le_rfl,hT.le⟩)]
    simp only [sub_zero, smul_eq_mul]
  have horder : ((N+1:ℕ):WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  obtain ⟨s,hs,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hT
    ((hF.of_le horder).mono hstep : ContDiffOn ℝ (N+1) F (Icc 0 T))
  rw [hpoly] at he
  change |F T - _| ≤ _
  rw [he, abs_div, abs_mul, sub_zero, abs_pow, abs_of_pos hT, Nat.abs_cast]
  have hsn : s ∈ Icc 0 T := ⟨hs.1.le,hs.2.le⟩
  have hval := (lieIterate f (N+1) (.var i)).value_bound
    (by norm_num : (0:ℚ) ≤ 1) (z s) (by simpa using hregion s hsn)
  have hcoeff : ((lieIterate f (N+1) (.var i)).majorant 1:ℝ) ≤
      ((C:ℝ)*d)^(N+1)*((N+1).factorial:ℝ) := by
    exact_mod_cast lieIterate_factorial f hC hd hfC hfd (N+1) i
  have hder : |iteratedDeriv (N+1) F s| ≤
      ((C:ℝ)*d)^(N+1)*((N+1).factorial:ℝ) := by
    rw [show iteratedDeriv (N+1) F s = (lieIterate f (N+1) (.var i)).value (z s) from
      lieIterate_derivative f (.var i) hS hz (N+1) (hstep hsn)]
    exact hval.trans hcoeff
  calc
    _ ≤ (((C:ℝ)*d)^(N+1)*((N+1).factorial:ℝ))*T^(N+1)/((N+1).factorial:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hder (by positivity))
        (by positivity)
    _ = ((C:ℝ)*d*T)^(N+1) := by
      have hn : ((N+1).factorial:ℝ) ≠ 0 := by positivity
      rw [mul_pow]
      field_simp
      simp [mul_pow]

/-- This is an exact infinite-series representation, not a fixed-order
approximation: its explicit coefficients converge to the actual solution.
The strict condition C*d*T < 1 is a sufficient convergence radius derived
above, not a tolerance or empirical allowance. -/
theorem partialFlow_tendsto (f : Fin n → Expr n) {C : ℚ} {d : ℕ}
    (hC : 0 ≤ C) (hd : 1 ≤ d)
    (hfC : ∀ i, (f i).majorant 1 ≤ C) (hfd : ∀ i, (f i).degree ≤ d)
    {z : ℝ → Fin n → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hz : ∀ t ∈ S, HasDerivAt z (fun i => (f i).value (z t)) t)
    (hsmooth : ContDiffOn ℝ ∞ z S) {T : ℝ} (hT : 0 < T)
    (hstep : Icc 0 T ⊆ S) (hregion : ∀ t ∈ Icc 0 T, ∀ i, |z t i| ≤ 1)
    (hradius : (C:ℝ)*d*T < 1) (i : Fin n) :
    Tendsto (fun N => partialFlow f (z 0) N T i) atTop (𝓝 (z T i)) := by
  have hn : 0 ≤ (C:ℝ)*d*T := by positivity
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hn hradius).comp
    (tendsto_add_atTop_nat 1)
  apply (tendsto_iff_dist_tendsto_zero).mpr
  apply squeeze_zero (fun N => dist_nonneg)
    (fun N => ?_) (by simpa using hp)
  simpa only [Real.dist_eq, abs_sub_comm] using
    partialFlow_error f hC hd hfC hfd hS hz hsmooth hT hstep hregion N i

end GNC.PolynomialODE.Expr
