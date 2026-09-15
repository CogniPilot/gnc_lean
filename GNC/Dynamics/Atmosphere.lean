import GNC.Dynamics.QuadraticDrag
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Exponential-density drag envelopes. The density, velocity, uncertain
scale and changing mass contributions remain separate. Numerical reference
enclosures are not assumed to follow from these pointwise theorems. -/
noncomputable section
open Real
open scoped RealInnerProductSpace
namespace GNC.Atmosphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def density (H r₀ : ℝ) (p : E) : ℝ := exp (-(‖p‖-r₀)/H)
def densityLinear (H : ℝ) (p h : E) : ℝ := -⟪p,h⟫/(‖p‖*H)

theorem density_ratio (H r₀ : ℝ) (p h : E) :
    density H r₀ (p+h)/density H r₀ p = density H ‖p‖ (p+h) := by
  unfold density
  rw [← Real.exp_sub]
  congr 1
  ring

theorem density_derivative {p : ℝ → E} {h : E} {t H r₀ : ℝ}
    (hp : HasDerivAt p h t) (hz : p t ≠ 0) :
    HasDerivAt (fun s => density H r₀ (p s))
      (density H r₀ (p t)*densityLinear H (p t) h) t := by
  convert (((Gravity.norm_derivative hp hz).sub_const r₀).neg.div_const H).exp using 1
  dsimp [density, densityLinear]
  ring

/-- Polynomial exponential bounds on a certified unit interval, using
mathlib's exponential remainder rather than recomputing its series. -/
theorem exp_envelopes {sigma ell x R : ℝ} (hs : |sigma| ≤ x) (hx : x ≤ 1)
    (hlin : |sigma-ell| ≤ R) :
    |exp sigma-1-ell| ≤ x^2+R ∧ |exp sigma-1| ≤ x+x^2 ∧
      |exp sigma| ≤ 1+x+x^2 := by
  have he := Real.abs_exp_sub_one_sub_id_le (hs.trans hx)
  have hsq : sigma^2 ≤ x^2 := by
    nlinarith [mul_self_le_mul_self (abs_nonneg sigma) hs, sq_abs sigma]
  have hr := abs_add_le (exp sigma-1-sigma) (sigma-ell)
  have hc := abs_add_le (exp sigma-1-sigma) sigma
  have hp := abs_add_le (exp sigma-1) 1
  simp only [sub_add_sub_cancel, sub_add_cancel, abs_one] at hr hc hp
  refine ⟨by linarith, by linarith, ?_⟩
  linarith

/-- Density ratio and linearization envelopes for every spatial perturbation
within one scale height. The norm remainder is global at nonzero p. -/
theorem density_envelopes (H : ℝ) (p h : E) (hH : 0 < H) (hp : p ≠ 0)
    (hsmall : ‖h‖/H ≤ 1) :
    |density H ‖p‖ (p+h)-1-densityLinear H p h| ≤
        (‖h‖/H)^2+‖h‖^2/(2*‖p‖*H) ∧
      |density H ‖p‖ (p+h)-1| ≤ ‖h‖/H+(‖h‖/H)^2 ∧
      |density H ‖p‖ (p+h)| ≤ 1+‖h‖/H+(‖h‖/H)^2 := by
  have hs : |-(‖p+h‖-‖p‖)/H| ≤ ‖h‖/H := by
    rw [abs_div, abs_neg, abs_of_pos hH]
    exact div_le_div_of_nonneg_right (QuadraticDrag.norm_change p h) hH.le
  have hl : |-(‖p+h‖-‖p‖)/H-densityLinear H p h| ≤ ‖h‖^2/(2*‖p‖*H) := by
    have hr := QuadraticDrag.norm_linear_remainder p h hp
    have hid : -(‖p+h‖-‖p‖)/H-densityLinear H p h =
        -(‖p+h‖-‖p‖-⟪p,h⟫/‖p‖)/H := by
      dsimp [densityLinear]
      ring
    rw [hid, abs_div, abs_neg, abs_of_pos hH, abs_of_nonneg hr.1]
    convert div_le_div_of_nonneg_right hr.2 hH.le using 1 <;> ring
  exact exp_envelopes hs hsmall hl

theorem density_envelopes_uniform (H : ℝ) (p h : E) {P lower : ℝ}
    (hH : 0 < H) (hr : 0 < lower) (hp : lower ≤ ‖p‖) (hh : ‖h‖ ≤ P)
    (hsmall : P/H ≤ 1) :
    |density H ‖p‖ (p+h)-1-densityLinear H p h| ≤
        (P/H)^2+P^2/(2*lower*H) ∧
      |density H ‖p‖ (p+h)-1| ≤ P/H+(P/H)^2 ∧
      |density H ‖p‖ (p+h)| ≤ 1+P/H+(P/H)^2 := by
  have hp0 : 0 < ‖p‖ := hr.trans_le hp
  have hratio := div_le_div_of_nonneg_right hh hH.le
  have hsquare : (‖h‖/H)^2 ≤ (P/H)^2 := by
    nlinarith [mul_self_le_mul_self (div_nonneg (norm_nonneg h) hH.le) hratio]
  have hs := density_envelopes H p h hH (norm_pos_iff.mp hp0) (hratio.trans hsmall)
  have hh2 : ‖h‖^2 ≤ P^2 := by nlinarith [mul_self_le_mul_self (norm_nonneg h) hh]
  have hf : ‖h‖^2/(2*‖p‖*H) ≤ P^2/(2*lower*H) := by
    calc
      _ ≤ P^2/(2*‖p‖*H) := div_le_div_of_nonneg_right hh2 (by positivity)
      _ ≤ P^2/(2*lower*H) := div_le_div_of_nonneg_left (sq_nonneg P)
        (by positivity) (by nlinarith)
  exact ⟨by linarith [hs.1], by linarith [hs.2.1], by linarith [hs.2.2]⟩

def productLinear (ell : ℝ) (w h : E) : E :=
  ell • QuadraticDrag.field w+QuadraticDrag.linear w h
def productRemainder (s ell : ℝ) (w h : E) : E :=
  s • QuadraticDrag.field (w+h)-QuadraticDrag.field w-productLinear ell w h

theorem density_linear_bound (H : ℝ) (p h : E) (hH : 0 < H) (hp : p ≠ 0) :
    |densityLinear H p h| ≤ ‖h‖/H := by
  have hr : 0 < ‖p‖ := norm_pos_iff.mpr hp
  dsimp [densityLinear]
  rw [abs_div, abs_neg, abs_mul, abs_of_pos hr, abs_of_pos hH]
  apply (div_le_iff₀ (mul_pos hr hH)).mpr
  convert abs_real_inner_le_norm p h using 1 <;> field_simp <;> ring

/-- Derivative of the actual density-times-speed-squared profile. -/
theorem product_derivative {p w : ℝ → E} {dp dw : E} {t H r₀ : ℝ}
    (hp : HasDerivAt p dp t) (hw : HasDerivAt w dw t)
    (hp0 : p t ≠ 0) (hw0 : w t ≠ 0) :
    HasDerivAt (fun s => density H r₀ (p s) • QuadraticDrag.field (w s))
      (density H r₀ (p t) • productLinear (densityLinear H (p t) dp) (w t) dw) t := by
  convert (density_derivative hp hp0).smul (QuadraticDrag.field_derivative hw hw0) using 1
  dsimp [productLinear]
  module

theorem product_derivative_all {p w : ℝ → E} {dp dw : E} {t H r₀ : ℝ}
    (hp : HasDerivAt p dp t) (hw : HasDerivAt w dw t) (hp0 : p t ≠ 0) :
    HasDerivAt (fun s => density H r₀ (p s) • QuadraticDrag.field (w s))
      (density H r₀ (p t) • productLinear (densityLinear H (p t) dp) (w t) dw) t := by
  convert (density_derivative hp hp0).smul (QuadraticDrag.field_derivative_all hw) using 1
  dsimp [productLinear]
  module

theorem product_identity (s ell : ℝ) (w h : E) :
    productRemainder s ell w h =
      (s-1-ell) • QuadraticDrag.field w+(s-1) • QuadraticDrag.linear w h+
        s • (QuadraticDrag.field (w+h)-QuadraticDrag.field w-QuadraticDrag.linear w h) := by
  dsimp [productRemainder, productLinear]
  module

theorem product_linear_bound (ell : ℝ) (w h : E) :
    ‖productLinear ell w h‖ ≤ |ell| * ‖w‖^2+2*‖w‖*‖h‖ := by
  exact (norm_add_le _ _).trans (add_le_add
    (by simp [norm_smul, QuadraticDrag.field_norm]) (QuadraticDrag.linear_bound w h))

/-- Density times quadratic drag, after subtracting both first derivatives. -/
theorem product_remainder_bound (s ell : ℝ) (w h : E) {R C S : ℝ}
    (hR : |s-1-ell| ≤ R) (hC : |s-1| ≤ C) (hS : |s| ≤ S) :
    ‖productRemainder s ell w h‖ ≤ R*‖w‖^2+C*(2*‖w‖*‖h‖)+S*‖h‖^2 := by
  rw [product_identity]
  have h1 : ‖(s-1-ell) • QuadraticDrag.field w‖ ≤ R*‖w‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, QuadraticDrag.field_norm]
    exact mul_le_mul_of_nonneg_right hR (sq_nonneg _)
  have h2 : ‖(s-1) • QuadraticDrag.linear w h‖ ≤ C*(2*‖w‖*‖h‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hC (QuadraticDrag.linear_bound w h) (norm_nonneg _)
      ((abs_nonneg _).trans hC)
  have h3 : ‖s • (QuadraticDrag.field (w+h)-QuadraticDrag.field w-QuadraticDrag.linear w h)‖ ≤
      S*‖h‖^2 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hS (QuadraticDrag.remainder_bound w h) (norm_nonneg _)
      ((abs_nonneg _).trans hS)
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)

def uncertainRemainder (gamma k s ell : ℝ) (w h : E) : E :=
  ((1+gamma)*(1+k)) • (s • QuadraticDrag.field (w+h))-
    QuadraticDrag.field w-productLinear ell w h-gamma • QuadraticDrag.field w

/-- Gamma is the common density-scale error; 1+k is the inverse mass ratio.
The retained model already includes gamma times the reference drag. -/
theorem uncertain_identity (gamma k s ell : ℝ) (w h : E) :
    uncertainRemainder gamma k s ell w h =
      (1+gamma) • productRemainder s ell w h+gamma • productLinear ell w h+
        (1+gamma) • (k • (s • QuadraticDrag.field (w+h))) := by
  dsimp [uncertainRemainder, productRemainder, productLinear]
  module

private theorem smul_bound {c C B : ℝ} {v : E} (hc : |c| ≤ C) (hv : ‖v‖ ≤ B) :
    ‖c • v‖ ≤ C*B := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul hc hv (norm_nonneg _) ((abs_nonneg _).trans hc)

/-- Nonlinear drag residual including density/state and mass coupling. -/
theorem uncertain_remainder_bound (gamma k s ell : ℝ) (w h : E) {G K S R L : ℝ}
    (hg : |gamma| ≤ G) (hk : |k| ≤ K) (hs : |s| ≤ S)
    (hr : ‖productRemainder s ell w h‖ ≤ R) (hl : ‖productLinear ell w h‖ ≤ L) :
    ‖uncertainRemainder gamma k s ell w h‖ ≤
      (1+G)*R+G*L+(1+G)*K*S*(‖w‖+‖h‖)^2 := by
  have hg1 : |1+gamma| ≤ 1+G := by
    have h := abs_add_le (1:ℝ) gamma
    norm_num at h
    linarith
  have hnew : ‖QuadraticDrag.field (w+h)‖ ≤ (‖w‖+‖h‖)^2 := by
    rw [QuadraticDrag.field_norm]
    nlinarith [mul_self_le_mul_self (norm_nonneg (w+h)) (norm_add_le w h)]
  have h1 := smul_bound hg1 hr
  have h2 := smul_bound hg hl
  have h3 := smul_bound hg1 (smul_bound hk (smul_bound hs hnew))
  rw [uncertain_identity]
  have ht := (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
  convert ht using 1 <;> ring

theorem relative_wind_change (W : E →L[ℝ] E) (p v dp dv : E) :
    (v+dv-W (p+dp))-(v-W p) = dv-W dp := by
  rw [map_add]
  abel

theorem relative_wind_bound (W : E →L[ℝ] E) (dp dv : E) {P V spin : ℝ}
    (hp : ‖dp‖ ≤ P) (hv : ‖dv‖ ≤ V) (hW : ‖W‖ ≤ spin) :
    ‖dv-W dp‖ ≤ V+spin*P := by
  have hw := ((W.le_opNorm dp).trans
    (mul_le_mul hW hp (norm_nonneg _) ((norm_nonneg _).trans hW)))
  exact (norm_sub_le _ _).trans (add_le_add hv hw)

/-- A uniform envelope for the actual density/speed/mass residual. Its
scalar inputs can be supplied by `density_envelopes_uniform` and a wind
perturbation bound; no sampled state derivative appears in the hypotheses. -/
theorem uncertain_remainder_uniform (gamma k s ell : ℝ) (w h : E)
    {G K S R C x W D : ℝ}
    (hg : |gamma| ≤ G) (hk : |k| ≤ K) (hs : |s| ≤ S)
    (hr : |s-1-ell| ≤ R) (hc : |s-1| ≤ C) (hx : |ell| ≤ x)
    (hw : ‖w‖ ≤ W) (hh : ‖h‖ ≤ D) :
    ‖uncertainRemainder gamma k s ell w h‖ ≤
      (1+G)*(R*W^2+C*(2*W*D)+S*D^2)+G*(x*W^2+2*W*D)+
        (1+G)*K*S*(W+D)^2 := by
  have hW : 0 ≤ W := (norm_nonneg _).trans hw
  have hD : 0 ≤ D := (norm_nonneg _).trans hh
  have hsW : ‖w‖^2 ≤ W^2 := by nlinarith [mul_self_le_mul_self (norm_nonneg w) hw]
  have hsD : ‖h‖^2 ≤ D^2 := by nlinarith [mul_self_le_mul_self (norm_nonneg h) hh]
  have hWD : 2*‖w‖*‖h‖ ≤ 2*W*D := by
    have h := mul_le_mul hw hh (norm_nonneg _) hW
    nlinarith
  have hR := (abs_nonneg _).trans hr
  have hC := (abs_nonneg _).trans hc
  have hS := (abs_nonneg _).trans hs
  have hG := (abs_nonneg _).trans hg
  have hK := (abs_nonneg _).trans hk
  have hprod : ‖productRemainder s ell w h‖ ≤ R*W^2+C*(2*W*D)+S*D^2 :=
    (product_remainder_bound s ell w h hr hc hs).trans
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsW hR)
        (mul_le_mul_of_nonneg_left hWD hC)) (mul_le_mul_of_nonneg_left hsD hS))
  have hlin : ‖productLinear ell w h‖ ≤ x*W^2+2*W*D :=
    (product_linear_bound ell w h).trans (add_le_add
      (mul_le_mul hx hsW (sq_nonneg _) ((abs_nonneg _).trans hx)) hWD)
  have hsum : (‖w‖+‖h‖)^2 ≤ (W+D)^2 := by
    nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ ‖w‖+‖h‖) (add_le_add hw hh)]
  exact (uncertain_remainder_bound gamma k s ell w h hg hk hs hprod hlin).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left hsum (by positivity)) _)

end GNC.Atmosphere
