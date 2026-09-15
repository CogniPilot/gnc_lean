import GNC.Applications.OrbitalComparison.QuadraticPrediction
import GNC.Dynamics.GravityLipschitz

/-! A common a posteriori certificate for computed orbital predictors.
Any twice differentiable candidate is admissible, including a directional
Taylor/STT polynomial or an exact-angle response. Its actual differential
defect against the quadratic gravity field is combined with the proved
cubic remainder; neither method receives a prescribed numerical allowance.
-/
noncomputable section
open Set
namespace GNC.OrbitalComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def quadraticAcceleration (q p f : E) : E :=
  (360000:ℝ) • (Gravity.gradient mu q p+(1/2:ℝ) • Gravity.hessian mu q p p+f)

theorem numerical_gravity_defect (q p f a : E) {M δ : ℝ}
    (hM : M < 7000000) (hq : (7000000:ℝ) ≤ ‖q‖) (hp : ‖p‖ ≤ M)
    (hd : ‖a-quadraticAcceleration q p f‖ ≤ δ) :
    ‖a-nonlinearAcceleration q p f‖ ≤
      δ+360000*(4*mu/(7000000-M)^5)*M^3 := by
  have hMn : 0 ≤ M := (norm_nonneg p).trans hp
  have hμ : 0 < mu := by norm_num [mu]
  have hsep : 0 < 7000000-M := sub_pos.mpr hM
  have hr := (Gravity.remainder_cubic mu (by norm_num [mu]) q p hM hq hp).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg p) hp 3) (by positivity))
  have he : quadraticAcceleration q p f-nonlinearAcceleration q p f =
      -(360000:ℝ) • (Gravity.field mu (q+p)-Gravity.field mu q-
        Gravity.gradient mu q p-(1/2:ℝ) • Gravity.hessian mu q p p) := by
    dsimp [quadraticAcceleration,nonlinearAcceleration]
    module
  have hn : ‖quadraticAcceleration q p f-nonlinearAcceleration q p f‖ ≤
      360000*(4*mu/(7000000-M)^5)*M^3 := by
    rw [he,norm_smul,Real.norm_eq_abs]
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 360000)]
    exact (mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 360000)).trans_eq (by ring)
  exact (norm_sub_le_norm_sub_add_norm_sub a (quadraticAcceleration q p f) (nonlinearAcceleration q p f)).trans
    (add_le_add hd hn)

/-- A uniform defect bound certifies the *computed candidate*, rather than
only the ideal response it approximates. The existing physical tube and a
separately checked candidate radius justify the gravity Lipschitz constant.
All constants below are certificate inputs with explicit inequalities. -/
theorem PhysicalDeviation.numerical_prediction {q f : ℝ → E}
    (X : PhysicalDeviation q f) (p v a : ℝ → E) {M δ : ℝ}
    (hM : M < 7000000) (hactual : (Direct.tubeRadius:ℝ) ≤ M)
    (hlip : 360000*(2*mu/(7000000-M)^3) ≤ 17/20)
    (hδ : 0 ≤ δ)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ≤ (Direct.thrust:ℝ)*(7/20))
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (a t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0)
    (hr : ∀ t ∈ Icc (0:ℝ) 1, ‖p t‖ ≤ M)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, ‖a t-quadraticAcceleration (q t) (p t) (f t)‖ ≤ δ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-p t‖ ≤ (Direct.positionGain:ℝ)*
        (δ+360000*(4*mu/(7000000-M)^5)*M^3) ∧
      ‖X.v t-v t‖/600 ≤ (Direct.velocityGain:ℝ)/600*
        (δ+360000*(4*mu/(7000000-M)^5)*M^3) := by
  have hregion := physical_region q X.p X.v f X.continuous_p X.continuous_v
    hq hf X.derivative_p X.derivative_v X.initial_p X.initial_v
  have hMn : 0 ≤ M := (norm_nonneg (p 0)).trans (hr 0 (by norm_num))
  have hμ : 0 < mu := by norm_num [mu]
  have hsep : 0 < 7000000-M := sub_pos.mpr hM
  have hb := response_gain (fun t => X.p t-p t) (fun t => X.v t-v t)
    (fun t => nonlinearAcceleration (q t) (X.p t) (f t)-a t)
    (T := 1) (by norm_num)
    (C := δ+360000*(4*mu/(7000000-M)^5)*M^3) (by positivity)
    (X.continuous_p.sub hp) (X.continuous_v.sub hv)
    (fun t ht => (X.derivative_p t ht).sub (hdp t ht))
    (fun t ht => (X.derivative_v t ht).sub (hdv t ht))
    (by simp [X.initial_p,hip]) (by simp [X.initial_v,hiv]) (by
      intro t ht
      have hg := Gravity.field_difference_ball mu hμ.le (q t) (X.p t) (p t)
        (r := 7000000-M) (R := M) hsep (by simpa using hq t ht)
        ((hregion t ht).trans hactual) (hr t ht)
      have he : nonlinearAcceleration (q t) (X.p t) (f t)-
          nonlinearAcceleration (q t) (p t) (f t) =
          (360000:ℝ) • (Gravity.field mu (q t+X.p t)-Gravity.field mu (q t+p t)) := by
        dsimp [nonlinearAcceleration]
        module
      have hng : ‖nonlinearAcceleration (q t) (X.p t) (f t)-
          nonlinearAcceleration (q t) (p t) (f t)‖ ≤ (17/20)*‖X.p t-p t‖ := by
        rw [he,norm_smul,Real.norm_eq_abs]
        norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 360000)]
        have hh := (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 360000)).trans
          (by simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right hlip (norm_nonneg (X.p t-p t)))
        exact hh
      have hnd := numerical_gravity_defect (q t) (p t) (f t) (a t) hM (hq t ht) (hr t ht) (hd t ht)
      rw [norm_sub_rev] at hnd
      exact (norm_sub_le_norm_sub_add_norm_sub _ (nonlinearAcceleration (q t) (p t) (f t)) _).trans
        (add_le_add hng hnd))
  intro t ht
  have h := hb t ht
  simp only [gain_values.1,gain_values.2] at h
  refine ⟨h.1,?_⟩
  exact (div_le_div_of_nonneg_right h.2 (by norm_num : (0:ℝ) ≤ 600)).trans_eq (by ring)

end GNC.OrbitalComparison
