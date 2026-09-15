import GNC.Applications.OrbitalComparison.PolynomialEnvelope
import GNC.Dynamics.GravityLipschitz

/-!
An a posteriori orbital certificate which does not assume a circular nominal
trajectory or a pre-existing bound on the actual orbit. A first-exit argument
closes the gravity region from the candidate's residual. The final bound
retains the residual's time profile. Time is normalized to [0,1]; the caller
supplies the square of the physical duration as `scale`.

The same theorem applies to prescribed inertial thrust and prescribed
reference-RTN thrust. The candidate must approximate the physical trajectory
for the selected thrust law, including the nominal trajectory when needed.
-/
noncomputable section
open Set
namespace GNC.OrbitalComparison
open Planning.PolynomialKernel PolynomialOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A coarse residual gain closes the region once, without iteration; the
time-profile envelope then gives the sharper reported prediction bound. -/
theorem regional_weighted_response (p v acc : ℝ → E) (f envelope : List ℚ)
    (henv : PolynomialEnvelope.Valid f envelope) (hf : nonnegative f) {M : ℝ}
    (hclose : shape 1 * ((evaluate f 1 : ℚ) : ℝ) < M)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (acc t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0)
    (ha : ∀ t ∈ Icc (0:ℝ) 1, ‖p t‖ ≤ M →
      ‖acc t‖ ≤ (17/20)*‖p t‖ + value f t) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖p t‖ ≤ ((evaluate envelope 1:ℚ):ℝ) ∧
      ‖v t‖ ≤ ((evaluate (differentiate envelope) 1:ℚ):ℝ) := by
  have hcast : value f 1 = ((evaluate f 1:ℚ):ℝ) := by
    simpa only [Rat.cast_one] using value_at_rational f 1
  have hfn : (0:ℝ) ≤ ((evaluate f 1:ℚ):ℝ) := by
    rw [← hcast]
    exact value_nonnegative f hf (by norm_num)
  have hMn : 0 < M := lt_of_le_of_lt
    (mul_nonneg (shape_bounds (show (1:ℝ) ∈ Icc 0 1 by norm_num)).1 hfn) hclose
  have hregion := IntegralTube.prefix_closure hp.norm
    (show ‖p 0‖ < M by simpa [hip] using hMn) (a := 0) (b := 1) (by
      intro t ht hprefix
      have hb := response_gain p v acc ht.2 hfn hp hv
        (fun s hs => hdp s ⟨hs.1,hs.2.trans ht.2⟩)
        (fun s hs => hdv s ⟨hs.1,hs.2.trans ht.2⟩) hip hiv (by
          intro s hs
          have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans ht.2⟩
          have hbound := value_le_endpoint f hf hs'
          rw [← hcast]
          exact (ha s hs' (hprefix s hs)).trans (add_le_add_right hbound _))
      exact (hb t ⟨ht.1,le_rfl⟩).1.trans_lt hclose)
  exact PolynomialEnvelope.response p v acc f envelope henv hp hv hdp hdv hip hiv
    (fun t ht => ha t ht (hregion t ht).le)

variable [InnerProductSpace ℝ E]

/-- Full inverse-square gravity, arbitrary prescribed thrust, and any smooth
candidate. The radius condition is a domain-of-validity check, not an added
position-error allowance. All quantities are in one common inertial frame. -/
theorem orbital_prediction (μ scale : ℝ) (hμ : 0 ≤ μ) (hscale : 0 ≤ scale)
    (x velocity q qv qa thrust : ℝ → E) (f envelope : List ℚ)
    (henv : PolynomialEnvelope.Valid f envelope) (hf : nonnegative f)
    {r M : ℝ} (hr : 0 < r)
    (hclose : shape 1 * ((evaluate f 1:ℚ):ℝ) < M)
    (hlip : scale*(2*μ/r^3) ≤ 17/20)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r+M ≤ ‖q t‖)
    (hx : Continuous x) (hv : Continuous velocity)
    (hcq : Continuous q) (hcqv : Continuous qv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (velocity t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt velocity (scale • (Gravity.field μ (x t)+thrust t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hip : x 0 = q 0) (hiv : velocity 0 = qv 0)
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1,
      ‖scale • (Gravity.field μ (q t)+thrust t)-qa t‖ ≤ value f t) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖x t-q t‖ ≤ ((evaluate envelope 1:ℚ):ℝ) ∧
      ‖velocity t-qv t‖ ≤ ((evaluate (differentiate envelope) 1:ℚ):ℝ) := by
  have hfn : (0:ℝ) ≤ ((evaluate f 1:ℚ):ℝ) := by
    have h := value_nonnegative f hf (show (0:ℝ) ≤ 1 by norm_num)
    simpa only [← value_at_rational f 1,Rat.cast_one] using h
  have hMn : 0 ≤ M := (lt_of_le_of_lt
    (mul_nonneg (shape_bounds (show (1:ℝ) ∈ Icc 0 1 by norm_num)).1 hfn) hclose).le
  apply regional_weighted_response (fun t => x t-q t) (fun t => velocity t-qv t)
    (fun t => scale • (Gravity.field μ (x t)+thrust t)-qa t) f envelope henv hf hclose
    (hx.sub hcq) (hv.sub hcqv)
    (fun t ht => (hdx t ht).sub (hdq t ht))
    (fun t ht => (hdv t ht).sub (hdqv t ht))
    (by simp [hip]) (by simp [hiv])
  intro t ht hreg
  have hg := Gravity.field_difference_ball μ hμ (q t) (x t-q t) 0 hr (hq t ht)
    hreg (by simpa using hMn)
  simp only [add_sub_cancel,add_zero,sub_zero] at hg
  have hs : ‖scale • (Gravity.field μ (x t)-Gravity.field μ (q t))‖ ≤
      (17/20)*‖x t-q t‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hscale]
    exact (mul_le_mul_of_nonneg_left hg hscale).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlip (norm_nonneg _))
  have he : scale • (Gravity.field μ (x t)+thrust t)-qa t =
      scale • (Gravity.field μ (x t)-Gravity.field μ (q t))+
      (scale • (Gravity.field μ (q t)+thrust t)-qa t) := by module
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hs (hdefect t ht))

end GNC.OrbitalComparison
