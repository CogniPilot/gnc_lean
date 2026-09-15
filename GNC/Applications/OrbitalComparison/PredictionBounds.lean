import GNC.Applications.OrbitalComparison.Envelopes
import GNC.Applications.OrbitalComparison.DirectCertificate
import GNC.Dynamics.GravityRemainderBall

/-! A direct physical certificate for the actual nonlinear inverse-square ODE.
Time is tau=t/600; velocity variables are 600 times SI velocity. The reference
gravity matrix may vary with time. A polynomial supersolution certifies its
response gain; a quadratic theorem closes the unknown displacement region.
The radius and prediction-error bounds are computed from the physical inputs.
No numerical propagator error is included or asserted to be zero: the predictor
below satisfies the displayed retained ODE exactly.
-/
noncomputable section
open Set Polynomial
namespace GNC.OrbitalComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def mu : ℝ := 398600441800000

theorem gain_values : shape 1 = (Direct.positionGain:ℝ) ∧
    shapeV 1 = (Direct.velocityGain:ℝ) := by
  norm_num [shape,shapeV,shapePolynomial,Direct.positionGain,Direct.velocityGain,
    derivative_add,derivative_mul,derivative_pow]

theorem gradient_normalized (q d : E) (hq : (7000000:ℝ) ≤ ‖q‖) :
    360000*‖Gravity.gradient mu q d‖ ≤ (17/20)*‖d‖ := by
  have hg := Gravity.gradient_bound mu (by norm_num [mu]) q d
  have hcoef : 2*mu/‖q‖^3 ≤ 2*mu/7000000^3 :=
    div_le_div_of_nonneg_left (by norm_num [mu]) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hq 3)
  have hb := mul_le_mul_of_nonneg_left
    (hg.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg d))) (by norm_num : (0:ℝ) ≤ 360000)
  have hc : 360000*(2*mu/7000000^3) ≤ (17/20:ℝ) := by norm_num [mu]
  nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg d)]

def nonlinearAcceleration (q p f : E) : E :=
  (360000:ℝ) • (Gravity.field mu (q+p)-Gravity.field mu q+f)

theorem curvature_nonneg : (0:ℝ) ≤ Direct.curvature := by
  norm_num [Direct.curvature,Direct.nominalRadius,Direct.positionGain,Direct.forceBudget,Direct.duration,Direct.pointingAngle,Direct.thrust,Direct.gravityParameter,Direct.referenceRadius,Direct.angularSpeed]

theorem normalized_remainder (q d : E) (hq : (7000000:ℝ) ≤ ‖q‖)
    (hd : ‖d‖ ≤ 2*(Direct.nominalRadius:ℝ)) :
    360000*‖Gravity.field mu (q+d)-Gravity.field mu q-Gravity.gradient mu q d‖ ≤
      (Direct.curvature:ℝ)*‖d‖^2 := by
  have hD : 2*(Direct.nominalRadius:ℝ) < 7000000 := by
    exact_mod_cast Direct.admissible.2.2.2
  have h := Gravity.remainder_quadratic mu (by norm_num [mu]) q d hD hq hd
  have he : (Direct.curvature:ℝ) = 360000*(3*mu/(7000000-2*(Direct.nominalRadius:ℝ))^4) := by
    norm_num [Direct.curvature,mu]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 360000)]

theorem regional_acceleration (q p f : E) {R : ℝ}
    (hq : (7000000:ℝ) ≤ ‖q‖) (hp : ‖p‖ ≤ R) (hR : R ≤ 2*(Direct.nominalRadius:ℝ))
    (hf : ‖f‖ ≤ (Direct.thrust:ℝ)*(7/20)) :
    ‖nonlinearAcceleration q p f‖ ≤
      (17/20)*‖p‖+(Direct.forceBudget:ℝ)+(Direct.curvature:ℝ)*R^2 := by
  let rem := Gravity.field mu (q+p)-Gravity.field mu q-Gravity.gradient mu q p
  have hn : ‖Gravity.field mu (q+p)-Gravity.field mu q+f‖ ≤
      ‖Gravity.gradient mu q p‖+‖rem‖+‖f‖ := by
    have he : Gravity.field mu (q+p)-Gravity.field mu q+f =
        (Gravity.gradient mu q p+rem)+f := by dsimp [rem]; abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hlin := gradient_normalized q p hq
  have hrem := normalized_remainder q p hq (hp.trans hR)
  have hquad := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hp 2) curvature_nonneg
  rw [nonlinearAcceleration,norm_smul,Real.norm_eq_abs]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 360000)]
  dsimp [rem] at hn
  have hfval : (Direct.forceBudget:ℝ) = 360000*(Direct.thrust:ℝ)*(7/20) := by
    norm_num [Direct.forceBudget,Direct.duration,Direct.pointingAngle,Direct.thrust,Direct.gravityParameter,Direct.referenceRadius,Direct.angularSpeed]
  rw [hfval]
  linarith

/-- Actual displacement is bounded by the directly computed rational radius.
The region used for gravity is derived as twice the retained-response bound;
it is closed by first exit and then sharpened by the quadratic root theorem. -/
theorem physical_region (q p v f : ℝ → E)
    (hp : Continuous p) (hv : Continuous v)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ≤ (Direct.thrust:ℝ)*(7/20))
    (hdp : ∀ t ∈ Icc 0 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc 0 1, HasDerivAt v (nonlinearAcceleration (q t) (p t) (f t)) t)
    (hip : p 0 = 0) (hiv : v 0 = 0) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖p t‖ ≤ (Direct.tubeRadius:ℝ) := by
  have hc := QuadraticTube.closedRadius?_sound Direct.computation
  have hbound := QuadraticTube.bound (f := fun t => ‖p t‖) (T := 1)
    (a := (Direct.nominalRadius:ℝ)) (b := (Direct.nonlinearGain:ℝ)) (by norm_num)
    (by exact_mod_cast hc.1) (by exact_mod_cast hc.2.1) (by exact_mod_cast hc.2.2.1)
    hp.norm (by simpa only [hip,norm_zero] using (show (0:ℝ) ≤ Direct.nominalRadius from
      le_of_lt (by exact_mod_cast hc.1)))
    (fun t _ => norm_nonneg (p t)) (by
      intro R hR t ht hprefix
      have hb := response_gain p v (fun s => nonlinearAcceleration (q s) (p s) (f s))
        ht.2 (C := (Direct.forceBudget:ℝ)+(Direct.curvature:ℝ)*R^2)
        (add_nonneg (by norm_num [Direct.forceBudget,Direct.duration,Direct.pointingAngle,Direct.thrust,Direct.gravityParameter,Direct.referenceRadius,Direct.angularSpeed]) (mul_nonneg curvature_nonneg (sq_nonneg R)))
        hp hv (fun s hs => hdp s ⟨hs.1,hs.2.trans ht.2⟩)
        (fun s hs => hdv s ⟨hs.1,hs.2.trans ht.2⟩) hip hiv (by
          intro s hs
          simpa only [add_assoc] using regional_acceleration _ _ _ (hq s ⟨hs.1,hs.2.trans ht.2⟩)
            (hprefix s hs) hR.2 (hf s ⟨hs.1,hs.2.trans ht.2⟩)) t ⟨ht.1,le_rfl⟩
      rw [gain_values.1] at hb
      convert hb.1 using 1
      simp only [Direct.nominalRadius,Direct.nonlinearGain,Rat.cast_mul]
      ring)
  exact fun t ht => (hbound t ht).trans hc.2.2.2.1

theorem gradient_sub (q u v : E) :
    Gravity.gradient mu q (u-v) = Gravity.gradient mu q u-Gravity.gradient mu q v := by
  simp [Gravity.gradient, inner_sub_right, mul_sub, sub_smul, smul_sub]
  module

/-- The same bound holds for geometric and classical predictors retaining the
same gravity gradient and exact thrust forcing. This is a physical ODE theorem,
not a certificate for a floating-point evaluation of that predictor. -/
theorem exact_forcing_prediction (q p v f y w : ℝ → E)
    (hp : Continuous p) (hv : Continuous v) (hy : Continuous y) (hw : Continuous w)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ≤ (Direct.thrust:ℝ)*(7/20))
    (hdp : ∀ t ∈ Icc 0 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc 0 1, HasDerivAt v (nonlinearAcceleration (q t) (p t) (f t)) t)
    (hdy : ∀ t ∈ Icc 0 1, HasDerivAt y (w t) t)
    (hdw : ∀ t ∈ Icc 0 1,
      HasDerivAt w ((360000:ℝ) • (Gravity.gradient mu (q t) (y t)+f t)) t)
    (hip : p 0 = 0) (hiv : v 0 = 0) (hiy : y 0 = 0) (hiw : w 0 = 0) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖p t-y t‖ < 117/1000 ∧ ‖v t-w t‖/600 < 418/1000000 := by
  have hregion := physical_region q p v f hp hv hq hf hdp hdv hip hiv
  have hc := QuadraticTube.closedRadius?_sound Direct.computation
  let b := fun t => Gravity.field mu (q t+p t)-Gravity.field mu (q t)-Gravity.gradient mu (q t) (p t)
  let acc := fun t => (360000:ℝ) • (Gravity.gradient mu (q t) (p t-y t)+b t)
  have hder (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun s => v s-w s) (acc t) t := by
    convert (hdv t ht).sub (hdw t ht) using 1
    simp only [acc, b, nonlinearAcceleration, gradient_sub, ← smul_sub]
    congr 1; module
  have hb := response_gain (fun t => p t-y t) (fun t => v t-w t) acc
    (C := (Direct.curvature:ℝ)*(Direct.tubeRadius:ℝ)^2) (by norm_num)
    (mul_nonneg curvature_nonneg (sq_nonneg _))
    (hp.sub hy) (hv.sub hw) (fun t ht => (hdp t ht).sub (hdy t ht)) hder
    (by simp [hip,hiy]) (by simp [hiv,hiw]) (by
      intro t ht
      have h1 := gradient_normalized (q t) (p t-y t) (hq t ht)
      have h2 := normalized_remainder (q t) (p t) (hq t ht)
        ((hregion t ht).trans hc.2.2.2.2.le)
      have h3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hregion t ht) 2) curvature_nonneg
      have hn := norm_add_le (Gravity.gradient mu (q t) (p t-y t)) (b t)
      change ‖(360000:ℝ) • (Gravity.gradient mu (q t) (p t-y t)+b t)‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 360000)]
      dsimp [b] at hn
      linarith)
  intro t ht
  have h := hb t ht
  rw [gain_values.1,gain_values.2] at h
  have hpos : (Direct.positionGain:ℝ)*((Direct.curvature:ℝ)*(Direct.tubeRadius:ℝ)^2) < 117/1000 := by
    have hn : (Direct.positionError:ℝ) < 117/1000 := by
      have hn := (Rat.cast_lt (K := ℝ)).2 Direct.numerical_enclosures.2.2.2.2.1
      norm_num at hn ⊢
      exact hn
    simpa [Direct.positionError,Direct.nonlinearGain,mul_assoc] using hn
  have hvel : (Direct.velocityGain:ℝ)*((Direct.curvature:ℝ)*(Direct.tubeRadius:ℝ)^2)/600 < 418/1000000 := by
    have hn : (Direct.velocityError:ℝ) < 418/1000000 := by
      have hn := (Rat.cast_lt (K := ℝ)).2 Direct.numerical_enclosures.2.2.2.2.2
      norm_num at hn ⊢
      exact hn
    simpa [Direct.velocityError,mul_assoc] using hn
  exact ⟨h.1.trans_lt hpos,
    (div_le_div_of_nonneg_right h.2 (by norm_num)).trans_lt hvel⟩

end GNC.OrbitalComparison
