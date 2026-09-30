import GNC.Analysis.SecondOrderBound
import GNC.Control.IntegralTube

/-! Transfer a prescribed-input navigation predictor to position-dependent gravity.

The acceleration defect is checked along the candidate, not the unknown orbit.
A regional Lipschitz bound and a first-exit argument give a noniterative physical
position/velocity certificate. This is a real-arithmetic theorem; computing a
certified defect for a floating-point implementation remains a separate task.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.PreintegrationGravityTransfer
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The dimensionless feedback denominator. Its positivity is a sufficient
step-size condition, not a numerical tolerance. -/
def denominator (K T : ℝ) : ℝ := 1-K*T^2/2

/-- Exact prescribed-input navigation propagation cancels the entire thrust
history in the physical defect. The prescribed gravity can be time varying. -/
theorem navigation_defect (gq ghat u qdd : E) (h : qdd = ghat+u) :
    gq+u-qdd = gq-ghat := by rw [h]; abel

/-- An explicit second-order residual bound, also valid when the residual is zero. -/
theorem residual_bound (e w a : ℝ → E) {T K ε : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hgain : K*T^2/2 < 1)
    (he : Continuous e) (hw : Continuous w)
    (hde : ∀ t ∈ Icc 0 T, HasDerivAt e (w t) t)
    (hdw : ∀ t ∈ Icc 0 T, HasDerivAt w (a t) t)
    (he0 : e 0 = 0) (hw0 : w 0 = 0)
    (ha : ∀ t ∈ Icc 0 T, ‖a t‖ ≤ K*‖e t‖+ε) :
    ∀ t ∈ Icc 0 T,
      ‖e t‖ ≤ (ε/denominator K T)*t^2/2 ∧
      ‖w t‖ ≤ (ε/denominator K T)*t := by
  have hD : 0 < denominator K T := by unfold denominator; linarith
  let P := (ε/denominator K T)*T^2/2
  have hid : K*P+ε = ε/denominator K T := by
    dsimp only [P]
    apply (eq_div_iff hD.ne').mpr
    field_simp [hD.ne']
    unfold denominator
    ring
  have hb := SecondOrderBound.small_gain e w a hT hK hε
    he.continuousOn hw.continuousOn
    (fun t ht => (hde t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => (hdw t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    he0 hw0 (fun t ht => ha t (Ico_subset_Icc_self ht)) hgain
    (P := P) (by rw [hid])
  apply SecondOrderBound.acceleration_bound e w a he.continuousOn hw.continuousOn
    (fun t ht => (hde t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => (hdw t (Ico_subset_Icc_self ht)).hasDerivWithinAt) he0 hw0
  intro t ht
  rw [← hid]
  exact (ha t (Ico_subset_Icc_self ht)).trans
    (add_le_add (mul_le_mul_of_nonneg_left
      (hb t (Ico_subset_Icc_self ht)).1 hK) le_rfl)

/-- Close the gravity region without assuming that the true trajectory stays
inside it. The strict region margin is geometric, not an added error budget. -/
theorem regional_residual_bound (e w a : ℝ → E) {T K ε M : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hgain : K*T^2/2 < 1)
    (hclose : (ε/denominator K T)*T^2/2 < M)
    (he : Continuous e) (hw : Continuous w)
    (hde : ∀ t ∈ Icc 0 T, HasDerivAt e (w t) t)
    (hdw : ∀ t ∈ Icc 0 T, HasDerivAt w (a t) t)
    (he0 : e 0 = 0) (hw0 : w 0 = 0)
    (ha : ∀ t ∈ Icc 0 T, ‖e t‖ ≤ M → ‖a t‖ ≤ K*‖e t‖+ε) :
    ∀ t ∈ Icc 0 T,
      ‖e t‖ ≤ (ε/denominator K T)*t^2/2 ∧
      ‖w t‖ ≤ (ε/denominator K T)*t := by
  have hD : 0 < denominator K T := by unfold denominator; linarith
  have hM : 0 < M := lt_of_le_of_lt (by positivity) hclose
  have hregion := IntegralTube.prefix_closure he.norm (a := 0) (b := T)
    (by simpa [he0] using hM) (by
      intro t ht hprefix
      have sub (s : ℝ) (hs : s ∈ Icc 0 t) : s ∈ Icc (0:ℝ) T :=
        ⟨hs.1, hs.2.trans ht.2⟩
      have ht2 : t^2 ≤ T^2 := by nlinarith [ht.1, ht.2]
      have hkt : K*t^2/2 ≤ K*T^2/2 := by nlinarith
      have hgt : K*t^2/2 < 1 := hkt.trans_lt hgain
      have hb := residual_bound e w a ht.1 hK hε hgt he hw
        (fun s hs => hde s (sub s hs)) (fun s hs => hdw s (sub s hs))
        he0 hw0 (fun s hs => ha s (sub s hs) (hprefix s hs)) t ⟨ht.1, le_rfl⟩
      have hden : denominator K T ≤ denominator K t := by
        unfold denominator; linarith
      have hratio : ε/denominator K t ≤ ε/denominator K T :=
        div_le_div_of_nonneg_left hε hD hden
      have hprod := mul_le_mul hratio ht2 (sq_nonneg t) (by positivity : 0 ≤ ε/denominator K T)
      exact hb.1.trans_lt ((by linarith :
        (ε/denominator K t)*t^2/2 ≤ (ε/denominator K T)*T^2/2).trans_lt hclose))
  exact residual_bound e w a hT hK hε hgain he hw hde hdw he0 hw0
    (fun t ht => ha t ht (hregion t ht).le)

/-- Physical orbital conversion: the navigation predictor uses the same
prescribed thrust `u`. Only its gravity/integration defect remains. Arbitrary
time-dependent gravity is allowed, provided the regional spatial bound holds.
No assumed exactness of an STM or of a linearized orbital model is used. -/
theorem physical_transfer (g : ℝ → E → E) (u p v q z qdd : ℝ → E)
    {T K ε M : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hgain : K*T^2/2 < 1) (hclose : (ε/denominator K T)*T^2/2 < M)
    (hp : Continuous p) (hv : Continuous v) (hq : Continuous q) (hz : Continuous z)
    (hdp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc 0 T, HasDerivAt v (g t (p t)+u t) t)
    (hdq : ∀ t ∈ Icc 0 T, HasDerivAt q (z t) t)
    (hdz : ∀ t ∈ Icc 0 T, HasDerivAt z (qdd t) t)
    (hp0 : p 0 = q 0) (hv0 : v 0 = z 0)
    (hlip : ∀ t ∈ Icc 0 T, ∀ x, ‖x-q t‖ ≤ M →
      ‖g t x-g t (q t)‖ ≤ K*‖x-q t‖)
    (hdefect : ∀ t ∈ Icc 0 T, ‖g t (q t)+u t-qdd t‖ ≤ ε) :
    ∀ t ∈ Icc 0 T,
      ‖p t-q t‖ ≤ (ε/denominator K T)*t^2/2 ∧
      ‖v t-z t‖ ≤ (ε/denominator K T)*t := by
  apply regional_residual_bound (fun t => p t-q t) (fun t => v t-z t)
    (fun t => g t (p t)+u t-qdd t) hT hK hε hgain hclose
    (hp.sub hq) (hv.sub hz)
    (fun t ht => (hdp t ht).sub (hdq t ht))
    (fun t ht => (hdv t ht).sub (hdz t ht))
    (by simp [hp0]) (by simp [hv0])
  intro t ht hreg
  have hid : g t (p t)+u t-qdd t =
      (g t (p t)-g t (q t))+(g t (q t)+u t-qdd t) := by abel
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add (hlip t ht (p t) hreg) (hdefect t ht))

omit [NormedSpace ℝ E] in
/-- The spatial constants add for a finite collection of gravity sources.
Their locations and strengths may vary with time: apply this at each time. -/
theorem sum_spatial_bound {ι : Type*} (S : Finset ι) (g : ι → E → E)
    (K : ι → ℝ) (x y : E)
    (h : ∀ i ∈ S, ‖g i x-g i y‖ ≤ K i*‖x-y‖) :
    ‖(∑ i ∈ S, g i x)-(∑ i ∈ S, g i y)‖ ≤ (∑ i ∈ S, K i)*‖x-y‖ := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum h)

end GNC.PreintegrationGravityTransfer
