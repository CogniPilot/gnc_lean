import GNC.Analysis.PolynomialBounds
import GNC.Control.IntegralTube
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Executable polynomial ODE defect certificates. The expression language
has exact rational constants and polynomial operations. A coefficient
proposal is untrusted; its residual and Lipschitz majorants are computed
again and connected to the actual real differential equation below.
-/
namespace GNC.PolynomialODE
open Planning.PolynomialKernel PolynomialBounds

inductive Expr (n : ℕ) where
  | constant : ℚ → Expr n
  | var : Fin n → Expr n
  | add : Expr n → Expr n → Expr n
  | multiply : Expr n → Expr n → Expr n
  | negate : Expr n → Expr n

namespace Expr
variable {n : ℕ}

noncomputable def value (e : Expr n) (x : Fin n → ℝ) : ℝ :=
  match e with
  | constant c => c
  | var i => x i
  | add a b => a.value x + b.value x
  | multiply a b => a.value x * b.value x
  | negate a => -a.value x

def coefficients (e : Expr n) (cs : Fin n → List ℚ) : List ℚ :=
  match e with
  | constant c => [c]
  | var i => cs i
  | add a b => PolynomialBounds.add (a.coefficients cs) (b.coefficients cs)
  | multiply a b => PolynomialBounds.multiply (a.coefficients cs) (b.coefficients cs)
  | negate a => PolynomialBounds.scale (-1) (a.coefficients cs)

def majorant (e : Expr n) (M : ℚ) : ℚ :=
  match e with
  | constant c => |c|
  | var _ => M
  | add a b => a.majorant M + b.majorant M
  | multiply a b => a.majorant M * b.majorant M
  | negate a => a.majorant M

def slope (e : Expr n) (M : ℚ) : ℚ :=
  match e with
  | constant _ => 0
  | var _ => 1
  | add a b => a.slope M + b.slope M
  | multiply a b => a.majorant M * b.slope M + b.majorant M * a.slope M
  | negate a => a.slope M

theorem majorant_nonneg (e : Expr n) {M : ℚ} (hM : 0 ≤ M) : 0 ≤ e.majorant M := by
  induction e <;> simp_all [majorant, add_nonneg, mul_nonneg, abs_nonneg]

theorem slope_nonneg (e : Expr n) {M : ℚ} (hM : 0 ≤ M) : 0 ≤ e.slope M := by
  induction e with
  | constant c => simp [slope]
  | var i => simp [slope]
  | add a b ha hb => exact add_nonneg ha hb
  | multiply a b ha hb =>
    exact add_nonneg (mul_nonneg (a.majorant_nonneg hM) hb)
      (mul_nonneg (b.majorant_nonneg hM) ha)
  | negate a ha => exact ha

theorem coefficients_correct (e : Expr n) (cs : Fin n → List ℚ) (t : ℝ) :
    evaluate ((e.coefficients cs).map (Rat.castHom ℝ)) t =
      e.value (fun i => evaluate ((cs i).map (Rat.castHom ℝ)) t) := by
  induction e with
  | constant c => simp [coefficients, value, evaluate]
  | var i => rfl
  | add a b ha hb => simp only [coefficients, add_map, evaluate_add, value, ha, hb]
  | multiply a b ha hb => simp only [coefficients, multiply_map, evaluate_multiply, value, ha, hb]
  | negate a ha =>
    simp only [coefficients, scale_map, evaluate_scale, value, ha, map_neg, map_one,
      neg_one_mul]

theorem value_bound (e : Expr n) {M : ℚ} (hM : 0 ≤ M) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ (M : ℝ)) : |e.value x| ≤ (e.majorant M : ℝ) := by
  induction e with
  | constant c => simp [value, majorant]
  | var i => exact hx i
  | add a b ha hb => simpa [value, majorant] using (abs_add_le (a.value x) (b.value x)).trans (add_le_add ha hb)
  | multiply a b ha hb =>
    simpa [value, majorant, abs_mul] using
      mul_le_mul ha hb (abs_nonneg _) (show (0:ℝ) ≤ (a.majorant M : ℝ) by exact_mod_cast a.majorant_nonneg hM)
  | negate a ha => simpa [value, majorant] using ha

theorem difference_bound (e : Expr n) {M : ℚ} (hM : 0 ≤ M)
    (x y : Fin n → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hx : ∀ i, |x i| ≤ (M : ℝ)) (hy : ∀ i, |y i| ≤ (M : ℝ))
    (hxy : ∀ i, |x i-y i| ≤ D) :
    |e.value x-e.value y| ≤ (e.slope M : ℝ)*D := by
  induction e with
  | constant c => simp [value, slope]
  | var i => simpa [value, slope] using hxy i
  | add a b ha hb =>
    have ht := abs_add_le (a.value x-a.value y) (b.value x-b.value y)
    simp only [value, slope, Rat.cast_add]
    have he : a.value x+b.value x-(a.value y+b.value y) =
        (a.value x-a.value y)+(b.value x-b.value y) := by ring
    rw [he]
    nlinarith
  | multiply a b ha hb =>
    have hmA : (0:ℝ) ≤ (a.majorant M : ℝ) := by exact_mod_cast a.majorant_nonneg hM
    have hsA : (0:ℝ) ≤ (a.slope M : ℝ) := by exact_mod_cast a.slope_nonneg hM
    have h₁ := mul_le_mul (a.value_bound hM x hx) hb (abs_nonneg _) hmA
    have h₂ := mul_le_mul ha (b.value_bound hM y hy) (abs_nonneg _)
      (mul_nonneg hsA hD)
    have ht := abs_add_le (a.value x*(b.value x-b.value y))
      ((a.value x-a.value y)*b.value y)
    simp only [abs_mul] at ht
    have he : a.value x*b.value x-a.value y*b.value y =
        a.value x*(b.value x-b.value y)+(a.value x-a.value y)*b.value y := by ring
    simp only [value, slope, Rat.cast_add, Rat.cast_mul]
    rw [he]
    nlinarith
  | negate a ha =>
    change |-a.value x- -a.value y| ≤ (a.slope M:ℝ)*D
    rw [show -a.value x- -a.value y = -(a.value x-a.value y) by ring, abs_neg]
    exact ha

end Expr

variable {n : ℕ}

noncomputable def curve (cs : Fin n → List ℚ) (t : ℝ) : Fin n → ℝ :=
  fun i => evaluate ((cs i).map (Rat.castHom ℝ)) t

def residual (f : Fin n → Expr n) (cs : Fin n → List ℚ) (i : Fin n) : List ℚ :=
  PolynomialBounds.subtract (differentiate (cs i)) ((f i).coefficients cs)

/-- Soundness of the computed coefficient-sum defect for every real time in
the step. The bound is evaluated in exact rational arithmetic. -/
theorem residual_bound (f : Fin n → Expr n) (cs : Fin n → List ℚ)
    {h : ℚ} {t : ℝ} (ht : |t| ≤ (h : ℝ)) (i : Fin n) :
    |evaluate ((differentiate (cs i)).map (Rat.castHom ℝ)) t -
      (f i).value (curve cs t)| ≤ (PolynomialBounds.bound (residual f cs i) h : ℝ) := by
  have hb := PolynomialBounds.bound_sound (residual f cs i) ht
  unfold residual at hb
  rw [subtract_map, evaluate_subtract, Expr.coefficients_correct] at hb
  exact hb

theorem curve_derivative (cs : Fin n → List ℚ) (t : ℝ) :
    HasDerivAt (curve cs)
      (fun i => evaluate ((differentiate (cs i)).map (Rat.castHom ℝ)) t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [curve, ← differentiate_map] using
    PolynomialBounds.evaluate_hasDerivAt ((cs i).map (Rat.castHom ℝ)) t

structure Step (n : ℕ) where
  coefficients : Fin n → List ℚ
  duration : ℚ
  region : ℚ
  lipschitz : ℚ
  initialError : ℚ
  error : ℚ
  defect : ℚ

def Step.Valid (s : Step n) (f : Fin n → Expr n) : Prop :=
  0 ≤ s.duration ∧ 0 ≤ s.region ∧ 0 ≤ s.lipschitz ∧ 0 ≤ s.initialError ∧
  0 < s.error ∧ 0 ≤ s.defect ∧
  s.initialError+s.duration*(s.lipschitz*s.error+s.defect) < s.error ∧
  ∀ i, PolynomialBounds.bound (s.coefficients i) s.duration+s.error ≤ s.region ∧
    PolynomialBounds.bound (residual f s.coefficients i) s.duration ≤ s.defect ∧
    (f i).slope s.region ≤ s.lipschitz

instance (s : Step n) (f : Fin n → Expr n) : Decidable (s.Valid f) := by
  unfold Step.Valid
  infer_instance

/-- A strict rational step certificate encloses an existing real trajectory
throughout the step. The sup norm is intentional: each coordinate receives
the same certified absolute bound. No unchecked solver or sampled maximum
appears in the theorem's hypotheses. -/
theorem step_sound (s : Step n) (f : Fin n → Expr n) (hs : s.Valid f)
    (x : ℝ → Fin n → ℝ) (hx : Continuous x)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) s.duration,
      HasDerivAt x (fun i => (f i).value (x t)) t)
    (hi : ‖x 0-curve s.coefficients 0‖ ≤ (s.initialError : ℝ)) :
    ∀ t ∈ Set.Icc (0:ℝ) s.duration,
      ‖x t-curve s.coefficients t‖ < (s.error : ℝ) := by
  obtain ⟨hT,hM,hL,hE,hB,hD,hclose,hcheck⟩ := hs
  have hTr : (0:ℝ) ≤ s.duration := by exact_mod_cast hT
  have hLr : (0:ℝ) ≤ s.lipschitz := by exact_mod_cast hL
  have hBr : (0:ℝ) < s.error := by exact_mod_cast hB
  have hDr : (0:ℝ) ≤ s.defect := by exact_mod_cast hD
  have hCr : (0:ℝ) ≤ (s.lipschitz:ℝ)*s.error+s.defect := by positivity
  have hclosed : (s.initialError:ℝ)+(s.duration:ℝ)*
      ((s.lipschitz:ℝ)*s.error+s.defect) < s.error := by exact_mod_cast hclose
  have hc : Continuous (curve s.coefficients) := continuous_iff_continuousAt.mpr
    (fun t => (curve_derivative s.coefficients t).continuousAt)
  apply IntegralTube.prefix_closure ((hx.sub hc).norm)
    (hi.trans_lt (by nlinarith))
  intro t ht hpref
  have hdiff (u : ℝ) (hu : u ∈ Set.Icc 0 t) :
      ‖(fun i => (f i).value (x u))-
        (fun i => evaluate ((differentiate (s.coefficients i)).map (Rat.castHom ℝ)) u)‖ ≤
      (s.lipschitz:ℝ)*s.error+s.defect := by
    have hut : |u| ≤ (s.duration:ℝ) := by rw [abs_of_nonneg hu.1]; exact hu.2.trans ht.2
    have hp (i : Fin n) : |curve s.coefficients u i| ≤ (s.region:ℝ)-(s.error:ℝ) := by
      have hb := PolynomialBounds.bound_sound (s.coefficients i) hut
      have hr : (PolynomialBounds.bound (s.coefficients i) s.duration:ℝ)+s.error ≤ s.region :=
        by exact_mod_cast (hcheck i).1
      change |curve s.coefficients u i| ≤
        (PolynomialBounds.bound (s.coefficients i) s.duration:ℝ) at hb
      linarith
    have he (i : Fin n) : |x u i-curve s.coefficients u i| ≤ (s.error:ℝ) := by
      exact (show |x u i-curve s.coefficients u i| ≤ ‖x u-curve s.coefficients u‖ from
        by simpa [Real.norm_eq_abs] using norm_le_pi_norm (x u-curve s.coefficients u) i).trans (hpref u hu)
    have hxb (i : Fin n) : |x u i| ≤ (s.region:ℝ) := by
      have h := abs_add_le (x u i-curve s.coefficients u i) (curve s.coefficients u i)
      simp only [sub_add_cancel] at h
      linarith [hp i, he i]
    apply (pi_norm_le_iff_of_nonneg hCr).mpr
    intro i
    have hlip := (f i).difference_bound hM (x u) (curve s.coefficients u) hBr.le
      hxb (fun j => by linarith [hp j]) he
    have hres := residual_bound f s.coefficients hut i
    have hδ : (PolynomialBounds.bound (residual f s.coefficients i) s.duration:ℝ) ≤ s.defect :=
      by exact_mod_cast (hcheck i).2.1
    have hSlope : ((f i).slope s.region:ℝ) ≤ s.lipschitz := by exact_mod_cast (hcheck i).2.2
    have hadd := abs_add_le ((f i).value (x u)-(f i).value (curve s.coefficients u))
      ((f i).value (curve s.coefficients u)-
        evaluate ((differentiate (s.coefficients i)).map (Rat.castHom ℝ)) u)
    simp only [sub_add_sub_cancel] at hadd
    rw [abs_sub_comm] at hres
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_right hSlope hBr.le]
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu => ((hd u ⟨hu.1, hu.2.trans ht.2⟩).sub
      (curve_derivative s.coefficients u)).hasDerivWithinAt)
    (fun u hu => hdiff u (Set.Ico_subset_Icc_self hu)) t (Set.right_mem_Icc.mpr ht.1)
  simp only [sub_zero, Pi.sub_apply] at hm
  have hn := norm_sub_norm_le (x t-curve s.coefficients t) (x 0-curve s.coefficients 0)
  nlinarith [mul_le_mul_of_nonneg_left ht.2 hCr]

end GNC.PolynomialODE
