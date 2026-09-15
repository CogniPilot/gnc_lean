import GNC.Applications.OrbitalComparison.NumericalPrediction
import GNC.Applications.OrbitalComparison.PolynomialEnvelope

/-! Time-profile certificates for computed finite-burn predictions.
The cubic gravity remainder retains its t^6 factor when the candidate
starts with zero position and velocity. The same nonlinear-field Lipschitz
region and scalar polynomial envelope are used for either predictor.
-/
noncomputable section
open Set
namespace GNC.OrbitalComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem numerical_gravity_profile (q p f a : E) {M δ t : ℝ}
    (hM : M < 7000000) (hq : (7000000:ℝ) ≤ ‖q‖) (hr : ‖p‖ ≤ M)
    (hp : ‖p‖ ≤ M*t^2) (hd : ‖a-quadraticAcceleration q p f‖ ≤ δ) :
    ‖a-nonlinearAcceleration q p f‖ ≤
      δ+360000*(4*mu/(7000000-M)^5)*M^3*t^6 := by
  have hMn : 0 ≤ M := (norm_nonneg p).trans hr
  have hμ : 0 < mu := by norm_num [mu]
  have hsep : 0 < 7000000-M := sub_pos.mpr hM
  have hc : ‖p‖^3 ≤ M^3*t^6 := by
    convert pow_le_pow_left₀ (norm_nonneg p) hp 3 using 1 <;> ring
  have hb := (Gravity.remainder_cubic mu hμ.le q p hM hq hr).trans
    (mul_le_mul_of_nonneg_left hc (by positivity))
  have he : quadraticAcceleration q p f-nonlinearAcceleration q p f =
      -(360000:ℝ) • (Gravity.field mu (q+p)-Gravity.field mu q-
        Gravity.gradient mu q p-(1/2:ℝ) • Gravity.hessian mu q p p) := by
    dsimp [quadraticAcceleration,nonlinearAcceleration]
    module
  have hn : ‖quadraticAcceleration q p f-nonlinearAcceleration q p f‖ ≤
      360000*(4*mu/(7000000-M)^5)*M^3*t^6 := by
    rw [he,norm_smul,Real.norm_eq_abs]
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 360000)]
    exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 360000)).trans_eq (by ring)
  exact (norm_sub_le_norm_sub_add_norm_sub a (quadraticAcceleration q p f) _).trans
    (add_le_add hd hn)

theorem PhysicalDeviation.weighted_prediction {q f : ℝ → E}
    (X : PhysicalDeviation q f) (p v a : ℝ → E) (forcing envelope : List ℚ)
    (henv : PolynomialEnvelope.Valid forcing envelope) {M : ℝ}
    (hM : M < 7000000) (hactual : (Direct.tubeRadius:ℝ) ≤ M)
    (hlip : 360000*(2*mu/(7000000-M)^3) ≤ 17/20)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ≤ (Direct.thrust:ℝ)*(7/20))
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (a t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0)
    (hr : ∀ t ∈ Icc (0:ℝ) 1, ‖p t‖ ≤ M)
    (hd : ∀ t ∈ Icc (0:ℝ) 1,
      ‖a t-nonlinearAcceleration (q t) (p t) (f t)‖ ≤ PolynomialOrder.value forcing t) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-p t‖ ≤ ((Planning.PolynomialKernel.evaluate envelope 1:ℚ):ℝ) ∧
      ‖X.v t-v t‖/600 ≤
        ((Planning.PolynomialKernel.evaluate (Planning.PolynomialKernel.differentiate envelope) 1/600:ℚ):ℝ) := by
  have hregion := physical_region q X.p X.v f X.continuous_p X.continuous_v
    hq hf X.derivative_p X.derivative_v X.initial_p X.initial_v
  have hμ : 0 < mu := by norm_num [mu]
  have hsep : 0 < 7000000-M := sub_pos.mpr hM
  have hb := PolynomialEnvelope.response (fun t => X.p t-p t) (fun t => X.v t-v t)
    (fun t => nonlinearAcceleration (q t) (X.p t) (f t)-a t) forcing envelope henv
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
        exact (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 360000)).trans
          (by simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right hlip (norm_nonneg (X.p t-p t)))
      have hnd := hd t ht
      rw [norm_sub_rev] at hnd
      exact (norm_sub_le_norm_sub_add_norm_sub _ (nonlinearAcceleration (q t) (p t) (f t)) _).trans
        (add_le_add hng hnd))
  intro t ht
  have h := hb t ht
  refine ⟨h.1,?_⟩
  have he := div_le_div_of_nonneg_right h.2 (by norm_num : (0:ℝ) ≤ 600)
  simpa only [Rat.cast_div,Rat.cast_ofNat] using he

end GNC.OrbitalComparison
