import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-! Differential comparison and backstepping energy estimates.
These are mathematical control-theory results, independent of a vehicle model.
-/
noncomputable section
open Set Real
open scoped Topology
namespace GNC.Lyapunov

/-- Finite-interval comparison: neither the ODE nor its inequalities are
required before the initial time or after the horizon. -/
theorem exponential_bound_on {V dV : ℝ → ℝ} {c a b : ℝ}
    (hV : ∀ t ∈ Icc a b, HasDerivAt V (dV t) t)
    (hd : ∀ t ∈ Ico a b, dV t ≤ -c*V t) :
    ∀ t ∈ Icc a b, V t ≤ V a*exp (-c*(t-a)) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (f := V) (f' := dV) (δ := V a) (K := -c) (ε := 0)
    (fun t ht => (hV t ht).continuousAt.continuousWithinAt)
    (fun t ht r hr => (hV t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt.liminf_right_slope_le hr)
    (le_refl _) (fun t ht => by simpa using hd t ht)
  simpa only [gronwallBound_ε0] using h

theorem disturbed_bound_on {V dV : ℝ → ℝ} {c ε a b : ℝ} (hc : c ≠ 0)
    (hV : ∀ t ∈ Icc a b, HasDerivAt V (dV t) t)
    (hd : ∀ t ∈ Ico a b, dV t ≤ -c*V t+ε) :
    ∀ t ∈ Icc a b, V t ≤ V a*exp (-c*(t-a))+(ε/c)*(1-exp (-c*(t-a))) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (f := V) (f' := dV) (δ := V a) (K := -c) (ε := ε)
    (fun t ht => (hV t ht).continuousAt.continuousWithinAt)
    (fun t ht r hr => (hV t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt.liminf_right_slope_le hr)
    (le_refl _) hd
  intro t ht
  convert h t ht using 1
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hc)]
  simp only [div_neg]
  ring

/-- Differential Lyapunov comparison, reusing mathlib's Grönwall theorem.
The derivative coefficient may be negative. -/
theorem exponential_bound {V dV : ℝ → ℝ} {c a b : ℝ}
    (hV : ∀ t, HasDerivAt V (dV t) t)
    (hd : ∀ t ∈ Ico a b, dV t ≤ -c * V t) :
    ∀ t ∈ Icc a b, V t ≤ V a * exp (-c * (t-a)) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (f := V) (f' := dV) (δ := V a) (K := -c) (ε := 0)
    ((continuous_iff_continuousAt.mpr fun t => (hV t).continuousAt).continuousOn)
    (fun t _ r hr => (hV t).hasDerivWithinAt.liminf_right_slope_le hr)
    (le_refl _) (fun t ht => by simpa using hd t ht)
  simpa only [gronwallBound_ε0] using h

/-- A constant residual budget gives an explicit ultimate-energy bound. -/
theorem disturbed_bound {V dV : ℝ → ℝ} {c ε a b : ℝ} (hc : c ≠ 0)
    (hV : ∀ t, HasDerivAt V (dV t) t)
    (hd : ∀ t ∈ Ico a b, dV t ≤ -c * V t + ε) :
    ∀ t ∈ Icc a b,
      V t ≤ V a * exp (-c*(t-a)) + (ε/c)*(1-exp (-c*(t-a))) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (f := V) (f' := dV) (δ := V a) (K := -c) (ε := ε)
    ((continuous_iff_continuousAt.mpr fun t => (hV t).continuousAt).continuousOn)
    (fun t _ r hr => (hV t).hasDerivWithinAt.liminf_right_slope_le hr)
    (le_refl _) hd
  intro t ht
  convert h t ht using 1
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hc)]
  simp only [div_neg]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Young's inequality in a real inner-product space, with explicit weight. -/
theorem inner_young (x y : E) {k : ℝ} (hk : 0 < k) :
    inner ℝ x y ≤ (k/2)*‖x‖^2 + (1/(2*k))*‖y‖^2 := by
  have h := real_inner_le_norm x y
  have hs := sq_nonneg (k*‖x‖-‖y‖)
  have hy : ‖x‖*‖y‖ ≤ (k^2*‖x‖^2+‖y‖^2)/(2*k) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  convert h.trans hy using 1
  field_simp

def energy (p v r : E) : ℝ := (‖p‖^2+‖v‖^2+‖r‖^2)/2

theorem disturbance_dissipation (x f d : E) {k : ℝ} (hk : 0 < k)
    (hf : inner ℝ x f ≤ -k*‖x‖^2) :
    inner ℝ x (f+d) ≤ -(k/2)*‖x‖^2+‖d‖^2/(2*k) := by
  rw [inner_add_right]
  have h := inner_young x d hk
  ring_nf at h hf ⊢
  linarith

/-- A bounded additive disturbance yields a quantitative ultimate-energy
bound for a dissipative vector field. This is a proved comparison result,
not an asymptotic big-O claim. -/
theorem disturbed_energy_bound {x d : ℝ → E} (f : ℝ → E → E)
    {k δ a b : ℝ} (hk : 0 < k) (hδ : 0 ≤ δ)
    (hf : ∀ t y, inner ℝ y (f t y) ≤ -k*‖y‖^2)
    (hd : ∀ t, ‖d t‖ ≤ δ)
    (hx : ∀ t, HasDerivAt x (f t (x t)+d t) t) :
    ∀ t ∈ Icc a b, ‖x t‖^2/2 ≤
      (‖x a‖^2/2)*exp (-k*(t-a))+
      (δ^2/(2*k^2))*(1-exp (-k*(t-a))) := by
  have hder : ∀ t, HasDerivAt (fun u => ‖x u‖^2/2)
      (inner ℝ (x t) (f t (x t)+d t)) t := by
    intro t
    convert (hx t).norm_sq.div_const 2 using 1
    ring
  have h := disturbed_bound (c := k) (ε := δ^2/(2*k)) (a := a) (b := b)
    hk.ne' hder (by
      intro t ht
      have hpoint := disturbance_dissipation (x t) (f t (x t)) (d t) hk (hf t (x t))
      have hsq : ‖d t‖^2 ≤ δ^2 := by nlinarith [hd t, norm_nonneg (d t)]
      have hdiv := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 2*k)
      nlinarith)
  convert h using 1 <;> congr 2 <;> field_simp <;> ring

/-- Two-stage geometric backstepping with the actual coupling adjoint.
This is the energy theorem for log attitude and angular-rate tracking error. -/
theorem two_stage_exponential {q z : ℝ → E} (B Bt : ℝ → E →L[ℝ] E)
    {kq kz k a b : ℝ} (hkq : k ≤ kq) (hkz : k ≤ kz)
    (hB : ∀ t x y, inner ℝ x (B t y) = inner ℝ y (Bt t x))
    (hq : ∀ t, HasDerivAt q (-kq • q t+B t (z t)) t)
    (hz : ∀ t, HasDerivAt z (-kz • z t-Bt t (q t)) t) :
    ∀ t ∈ Icc a b, (‖q t‖^2+‖z t‖^2)/2 ≤
      ((‖q a‖^2+‖z a‖^2)/2)*exp (-2*k*(t-a)) := by
  have hd : ∀ t, HasDerivAt (fun s => (‖q s‖^2+‖z s‖^2)/2)
      (-kq*‖q t‖^2-kz*‖z t‖^2) t := by
    intro t
    convert ((hq t).norm_sq.add (hz t).norm_sq).div_const 2 using 1
    simp only [inner_add_right, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hB t]
    ring
  have h := exponential_bound (c := 2*k) (a := a) (b := b) hd (by
    intro t ht
    nlinarith [
      mul_nonneg (sub_nonneg.mpr hkq) (sq_nonneg ‖q t‖),
      mul_nonneg (sub_nonneg.mpr hkz) (sq_nonneg ‖z t‖)])
  simpa only [neg_mul] using h

/-- Exact three-stage backstepping cancellation, allowing a common
skew-adjoint transport S. Couplings are paired with their energy adjoints. -/
theorem backstepping_energy_identity (p v r : E)
    (S B Bt : E →L[ℝ] E) (kp kv kr : ℝ)
    (hS : ∀ x : E, inner ℝ x (S x) = 0)
    (hB : inner ℝ v (B r) = inner ℝ r (Bt v)) :
    inner ℝ p (S p - kp • p + v) +
      inner ℝ v (S v - p - kv • v + B r) +
      inner ℝ r (S r - Bt v - kr • r) =
      -kp*‖p‖^2-kv*‖v‖^2-kr*‖r‖^2 := by
  simp only [inner_add_right, inner_sub_right, inner_smul_right,
    hS, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v p, hB]
  ring

theorem energy_hasDerivAt {p v r : ℝ → E} {dp dv dr : E} {t : ℝ}
    (hp : HasDerivAt p dp t) (hv : HasDerivAt v dv t) (hr : HasDerivAt r dr t) :
    HasDerivAt (fun s => energy (p s) (v s) (r s))
      (inner ℝ (p t) dp + inner ℝ (v t) dv + inner ℝ (r t) dr) t := by
  convert (((hp.norm_sq).add hv.norm_sq).add hr.norm_sq).div_const 2 using 1
  ring

def weightedEnergy (wp wv wr : ℝ) (p v r : E) : ℝ :=
  (wp*‖p‖^2+wv*‖v‖^2+wr*‖r‖^2)/2

theorem triangular_weight_choice {kp kv kr : ℝ} (b : ℝ)
    (hkp : 0 < kp) (hkv : 0 < kv) (hkr : 0 < kr) :
    let wv := 2/(kp*kv)
    let wr := (1+b^2/(kp*kv^2))/kr
    0 < wv ∧ 0 < wr ∧
      wv*kv/2-1/(2*kp) = 1/(2*kp) ∧
      wr*kr-wv*b^2/(2*kv) = 1 := by
  dsimp
  refine ⟨by positivity, by positivity, ?_, ?_⟩ <;>
    field_simp <;> ring

theorem weightedEnergy_hasDerivAt {p v r : ℝ → E} {dp dv dr : E} {t : ℝ}
    (wp wv wr : ℝ)
    (hp : HasDerivAt p dp t) (hv : HasDerivAt v dv t) (hr : HasDerivAt r dr t) :
    HasDerivAt (fun s => weightedEnergy wp wv wr (p s) (v s) (r s))
      (wp*inner ℝ (p t) dp + wv*inner ℝ (v t) dv + wr*inner ℝ (r t) dr) t := by
  convert ((((hp.norm_sq).const_mul wp).add ((hv.norm_sq).const_mul wv)).add
    ((hr.norm_sq).const_mul wr)).div_const 2 using 1
  ring

/-- A complete pointwise bound for the original triangular cascade,
derived from Hilbert-space Young inequalities and the coupling norm bound. -/
theorem triangular_weighted_bound (p v r : E) (S B : E →L[ℝ] E)
    {kp kv kr wp wv wr b : ℝ} (hkp : 0 < kp) (hkv : 0 < kv)
    (hwp : 0 ≤ wp) (hwv : 0 ≤ wv) (hb : 0 ≤ b)
    (hS : ∀ x : E, inner ℝ x (S x) = 0)
    (hB : ‖B r‖ ≤ b*‖r‖) :
    wp*inner ℝ p (S p-kp • p+v) +
      wv*inner ℝ v (S v-kv • v+B r) +
      wr*inner ℝ r (S r-kr • r) ≤
      -(wp*kp/2)*‖p‖^2 -
      (wv*kv/2-wp/(2*kp))*‖v‖^2 -
      (wr*kr-wv*b^2/(2*kv))*‖r‖^2 := by
  have h1 := mul_le_mul_of_nonneg_left (inner_young p v hkp) hwp
  have hsq : ‖B r‖^2 ≤ b^2*‖r‖^2 := by
    nlinarith [norm_nonneg (B r), norm_nonneg r]
  have h2 : inner ℝ v (B r) ≤ (kv/2)*‖v‖^2+(1/(2*kv))*(b^2*‖r‖^2) := by
    refine (inner_young v (B r) hkv).trans ?_
    gcongr
  have h2' := mul_le_mul_of_nonneg_left h2 hwv
  simp only [inner_add_right, inner_sub_right, inner_smul_right,
    hS, real_inner_self_eq_norm_sq]
  ring_nf at h1 h2' ⊢
  linarith

/-- Uniform exponential decay of the original triangular system with weights.
Positive coefficient margins can be attained without the paper's restrictive
unweighted gain condition. -/
theorem triangular_exponential {p v r : ℝ → E}
    (S B : ℝ → E →L[ℝ] E) {kp kv kr wp wv wr c b a T : ℝ}
    (hkp : 0 < kp) (hkv : 0 < kv) (hwp : 0 ≤ wp) (hwv : 0 ≤ wv) (hb : 0 ≤ b)
    (hc1 : c*wp ≤ wp*kp/2)
    (hc2 : c*wv ≤ wv*kv/2-wp/(2*kp))
    (hc3 : c*wr ≤ wr*kr-wv*b^2/(2*kv))
    (hS : ∀ t x, inner ℝ x (S t x) = 0)
    (hB : ∀ t x, ‖B t x‖ ≤ b*‖x‖)
    (hp : ∀ t, HasDerivAt p (S t (p t)-kp • p t+v t) t)
    (hv : ∀ t, HasDerivAt v (S t (v t)-kv • v t+B t (r t)) t)
    (hr : ∀ t, HasDerivAt r (S t (r t)-kr • r t) t) :
    ∀ t ∈ Icc a T, weightedEnergy wp wv wr (p t) (v t) (r t) ≤
      weightedEnergy wp wv wr (p a) (v a) (r a) * exp (-2*c*(t-a)) := by
  have h := exponential_bound (c := 2*c) (a := a) (b := T)
    (fun t => weightedEnergy_hasDerivAt wp wv wr (hp t) (hv t) (hr t)) (by
      intro t ht
      have h0 := triangular_weighted_bound (p t) (v t) (r t) (S t) (B t)
        (kr := kr) (wr := wr) hkp hkv hwp hwv hb (hS t) (hB t (r t))
      dsimp [weightedEnergy]
      nlinarith [
        mul_le_mul_of_nonneg_right hc1 (sq_nonneg ‖p t‖),
        mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖v t‖),
        mul_le_mul_of_nonneg_right hc3 (sq_nonneg ‖r t‖)])
  simpa only [neg_mul] using h

/-- Exponential energy decay for the achieved backstepping cascade.
The skew/coupling identities are checked pointwise; the trajectory conclusion
uses actual derivatives and mathlib comparison, not a postulated decay bound. -/
theorem backstepping_exponential {p v r : ℝ → E}
    (S B Bt : ℝ → E →L[ℝ] E) {kp kv kr k a b : ℝ}
    (hkp : k ≤ kp) (hkv : k ≤ kv) (hkr : k ≤ kr)
    (hS : ∀ t x, inner ℝ x (S t x) = 0)
    (hB : ∀ t x y, inner ℝ x (B t y) = inner ℝ y (Bt t x))
    (hp : ∀ t, HasDerivAt p (S t (p t)-kp • p t+v t) t)
    (hv : ∀ t, HasDerivAt v (S t (v t)-p t-kv • v t+B t (r t)) t)
    (hr : ∀ t, HasDerivAt r (S t (r t)-Bt t (v t)-kr • r t) t) :
    ∀ t ∈ Icc a b, energy (p t) (v t) (r t) ≤
      energy (p a) (v a) (r a) * exp (-2*k*(t-a)) := by
  have hd : ∀ t, HasDerivAt (fun s => energy (p s) (v s) (r s))
      (-kp*‖p t‖^2-kv*‖v t‖^2-kr*‖r t‖^2) t := by
    intro t
    convert energy_hasDerivAt (hp t) (hv t) (hr t) using 1
    exact (backstepping_energy_identity _ _ _ _ _ _ _ _ _ (hS t)
      (hB t (v t) (r t))).symm
  have h := exponential_bound (c := 2*k) (a := a) (b := b) hd (by
    intro t ht
    dsimp [energy]
    nlinarith [sq_nonneg ‖p t‖, sq_nonneg ‖v t‖, sq_nonneg ‖r t‖,
      mul_nonneg (sub_nonneg.mpr hkp) (sq_nonneg ‖p t‖),
      mul_nonneg (sub_nonneg.mpr hkv) (sq_nonneg ‖v t‖),
      mul_nonneg (sub_nonneg.mpr hkr) (sq_nonneg ‖r t‖)])
  simpa only [neg_mul] using h

end GNC.Lyapunov
