import GNC.Applications.OrbitalComparison.SecondOrderComparison
import GNC.Dynamics.GravityQuadraticResponse
import GNC.Analysis.FiniteAngleReduction

/-! A uniform physical error certificate for the next exact-angle fidelity
level. The predictor is the first linear response plus the response forced
by its gravity Hessian. Numerical integration defects are separate.
-/
namespace GNC.OrbitalComparison.QuadraticBudget
open Direct

def acceleration : ℚ :=
  3*gravityParameter/referenceRadius^4*positionError*(tubeRadius+nominalRadius)+
    4*gravityParameter/(referenceRadius-2*nominalRadius)^5*tubeRadius^3
def position : ℚ := positionGain*duration^2*acceleration
def velocity : ℚ := velocityGain*duration*acceleration

theorem enclosures : 0 ≤ acceleration ∧ position < 41/1000000 ∧
    velocity < 143/1000000000 ∧ 2500*position < positionError := by
  norm_num [acceleration,position,velocity,gravityParameter,referenceRadius,positionError,
    tubeRadius,nominalRadius,nonlinearGain,curvature,positionGain,velocityGain,
    forceBudget,duration,pointingAngle,thrust,angularSpeed]
end GNC.OrbitalComparison.QuadraticBudget

noncomputable section
open Set
namespace GNC.OrbitalComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure PhysicalDeviation (q f : ℝ → E) where
  p : ℝ → E
  v : ℝ → E
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0 = 0
  initial_v : v 0 = 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt v (nonlinearAcceleration (q t) (p t) (f t)) t

/-- The quadratic correction is reusable across a whole angle family:
integrate its three coefficient responses once, then combine them. -/
def quadraticResponse {q fs fc : ℝ → E} (S : LinearResponse q fs) (C : LinearResponse q fc)
    (Qss : LinearResponse q (hessianForcing q S.p))
    (Qsc : LinearResponse q (fun t => Gravity.hessian mu (q t) (S.p t) (C.p t)))
    (Qcc : LinearResponse q (hessianForcing q C.p)) (s c : ℝ) :
    LinearResponse q (hessianForcing q (S.combine C s c).p) := by
  let R := (Qss.combine Qsc (s^2) (s*c)).combine Qcc 1 (c^2)
  have hforce (t : ℝ) : hessianForcing q (S.combine C s c).p t =
      (1:ℝ) • (s^2 • hessianForcing q S.p t+
        (s*c) • Gravity.hessian mu (q t) (S.p t) (C.p t))+
        c^2 • hessianForcing q C.p t := by
    simp only [hessianForcing,LinearResponse.combine,one_smul]
    exact Gravity.hessian_combination mu (q t) (S.p t) (C.p t) s c
  exact {
    p := R.p, v := R.v,
    continuous_p := R.continuous_p, continuous_v := R.continuous_v,
    initial_p := R.initial_p, initial_v := R.initial_v,
    derivative_p := R.derivative_p,
    derivative_v := by
      intro t ht
      rw [hforce]
      exact R.derivative_v t ht }

/-- The four-column query is exactly the certified quadratic predictor,
including its gravity correction, at every time and every real angle. -/
theorem quadraticResponse_reduced {q fs fc : ℝ → E}
    (S : LinearResponse q fs) (C : LinearResponse q fc)
    (Qss : LinearResponse q (hessianForcing q S.p))
    (Qsc : LinearResponse q (fun t => Gravity.hessian mu (q t) (S.p t) (C.p t)))
    (Qcc : LinearResponse q (hessianForcing q C.p)) (θ t : ℝ) :
    (S.combine C (Real.sin θ) (1-Real.cos θ)).p t+
      (quadraticResponse S C Qss Qsc Qcc (Real.sin θ) (1-Real.cos θ)).p t =
      FiniteAngleReduction.reduced (Real.sin θ) (1-Real.cos θ)
        (S.p t) (C.p t+2 • Qss.p t) (Qsc.p t) (Qcc.p t-Qss.p t) := by
  have h := FiniteAngleReduction.quadratic_reduction θ
    (S.p t) (C.p t) (Qss.p t) (Qsc.p t) (Qcc.p t)
  simpa [quadraticResponse,LinearResponse.combine,FiniteAngleReduction.quadratic,
    FiniteAngleComparison.exactAngle,add_assoc] using h

/-- Error transport by the actual known gravity-gradient equation. The
normalized residual C includes every forcing defect to be certified. -/
theorem residual_response_bound (q e v r : ℝ → E) {C : ℝ} (hC : 0 ≤ C)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (he : Continuous e) (hv : Continuous v)
    (hde : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt e (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt v ((360000:ℝ) • (Gravity.gradient mu (q t) (e t)+r t)) t)
    (hie : e 0 = 0) (hiv : v 0 = 0)
    (hr : ∀ t ∈ Icc (0:ℝ) 1, 360000*‖r t‖ ≤ C) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖e t‖ ≤ (Direct.positionGain:ℝ)*C ∧
      ‖v t‖ ≤ (Direct.velocityGain:ℝ)*C := by
  have hb := response_gain e v
    (fun t => (360000:ℝ) • (Gravity.gradient mu (q t) (e t)+r t))
    (by norm_num) hC he hv hde hdv hie hiv (by
      intro t ht
      have h1 := gradient_normalized (q t) (e t) (hq t ht)
      have h2 := norm_add_le (Gravity.gradient mu (q t) (e t)) (r t)
      rw [norm_smul,Real.norm_eq_abs]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 360000)]
      linarith [hr t ht])
  simpa only [gain_values.1,gain_values.2] using hb

theorem PhysicalDeviation.linear_error {q f : ℝ → E} (X : PhysicalDeviation q f)
    (Y : LinearResponse q f)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ≤ (Direct.thrust:ℝ)*(7/20)) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖X.p t-Y.p t‖ ≤ (Direct.positionError:ℝ) := by
  have hregion := physical_region q X.p X.v f X.continuous_p X.continuous_v
    hq hf X.derivative_p X.derivative_v X.initial_p X.initial_v
  have hrad := QuadraticTube.closedRadius?_sound Direct.computation
  let r := fun t => Gravity.field mu (q t+X.p t)-Gravity.field mu (q t)-
    Gravity.gradient mu (q t) (X.p t)
  have hb := residual_response_bound q (fun t => X.p t-Y.p t)
    (fun t => X.v t-Y.v t) r
    (C := (Direct.curvature:ℝ)*(Direct.tubeRadius:ℝ)^2)
    (mul_nonneg curvature_nonneg (sq_nonneg _)) hq
    (X.continuous_p.sub Y.continuous_p) (X.continuous_v.sub Y.continuous_v)
    (fun t ht => (X.derivative_p t ht).sub (Y.derivative_p t ht)) (by
      intro t ht
      convert (X.derivative_v t ht).sub (Y.derivative_v t ht) using 1
      simp only [r,nonlinearAcceleration,gradient_sub]
      module)
    (by simp [X.initial_p,Y.initial_p]) (by simp [X.initial_v,Y.initial_v]) (by
      intro t ht
      have hr := normalized_remainder (q t) (X.p t) (hq t ht)
        ((hregion t ht).trans hrad.2.2.2.2.le)
      exact hr.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hregion t ht) 2) curvature_nonneg))
  intro t ht
  simpa only [Direct.positionError,Direct.nonlinearGain,Rat.cast_mul,Rat.cast_pow,mul_assoc] using (hb t ht).1

/-- Both response stages use the same known reference. The Hessian is
evaluated on Y, so its difference from the actual state must be charged. -/
theorem PhysicalDeviation.quadratic_error {q f : ℝ → E} (X : PhysicalDeviation q f)
    (Y : LinearResponse q f) (Z : LinearResponse q (hessianForcing q Y.p))
    (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ≤ (Direct.thrust:ℝ)*(7/20)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-Y.p t-Z.p t‖ < 41/1000000 ∧
      ‖X.v t-Y.v t-Z.v t‖/600 < 143/1000000000 := by
  have hregion := physical_region q X.p X.v f X.continuous_p X.continuous_v
    hq hf X.derivative_p X.derivative_v X.initial_p X.initial_v
  have he := X.linear_error Y hq hf
  have hY := Y.bound (by norm_num [Direct.thrust,Direct.gravityParameter,
    Direct.referenceRadius,Direct.angularSpeed]) hq hf
  have hY' (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖Y.p t‖ ≤ (Direct.nominalRadius:ℝ) := by
    convert hY t ht using 1
    simp only [Direct.nominalRadius,Direct.forceBudget,Direct.duration,Direct.pointingAngle]
    push_cast
    ring
  have hrad := QuadraticTube.closedRadius?_sound Direct.computation
  let r := fun t => Gravity.quadraticResidual mu (q t) (X.p t) (Y.p t)
  have hr (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      360000*‖r t‖ ≤ 360000*(QuadraticBudget.acceleration:ℝ) := by
    have hb := Gravity.quadratic_residual_bound mu (by norm_num [mu])
      (q t) (X.p t) (Y.p t) (D := 2*(Direct.nominalRadius:ℝ))
      (by exact_mod_cast Direct.admissible.2.2.2) (hq t ht) (hregion t ht)
      hrad.2.2.2.2.le (hY' t ht) (he t ht)
    have hb' : ‖r t‖ ≤ (QuadraticBudget.acceleration:ℝ) := by
      convert hb using 1
      norm_num [QuadraticBudget.acceleration,Direct.gravityParameter,Direct.referenceRadius,mu]
    exact mul_le_mul_of_nonneg_left hb' (by norm_num)
  have hacc : (0:ℝ) ≤ QuadraticBudget.acceleration := by
    exact_mod_cast QuadraticBudget.enclosures.1
  have hb := residual_response_bound q (fun t => X.p t-Y.p t-Z.p t)
    (fun t => X.v t-Y.v t-Z.v t) r (by positivity) hq
    ((X.continuous_p.sub Y.continuous_p).sub Z.continuous_p)
    ((X.continuous_v.sub Y.continuous_v).sub Z.continuous_v)
    (fun t ht => ((X.derivative_p t ht).sub (Y.derivative_p t ht)).sub (Z.derivative_p t ht))
    (by
      intro t ht
      convert ((X.derivative_v t ht).sub (Y.derivative_v t ht)).sub (Z.derivative_v t ht) using 1
      simp only [r,Gravity.quadraticResidual,nonlinearAcceleration,hessianForcing,gradient_sub]
      module)
    (by simp [X.initial_p,Y.initial_p,Z.initial_p])
    (by simp [X.initial_v,Y.initial_v,Z.initial_v]) hr
  intro t ht
  have hp : (Direct.positionGain:ℝ)*(360000*(QuadraticBudget.acceleration:ℝ)) < 41/1000000 := by
    have hh : (QuadraticBudget.position:ℝ) < 41/1000000 := by
      have hh := (Rat.cast_lt (K := ℝ)).2 QuadraticBudget.enclosures.2.1
      norm_num at hh ⊢
      exact hh
    norm_num [QuadraticBudget.position,Direct.duration,mul_assoc] at hh
    exact hh
  have hv : (Direct.velocityGain:ℝ)*(360000*(QuadraticBudget.acceleration:ℝ))/600 <
      143/1000000000 := by
    have hh : (QuadraticBudget.velocity:ℝ) < 143/1000000000 := by
      have hh := (Rat.cast_lt (K := ℝ)).2 QuadraticBudget.enclosures.2.2.1
      norm_num at hh ⊢
      exact hh
    convert hh using 1
    simp only [QuadraticBudget.velocity,Direct.duration,Rat.cast_mul,Rat.cast_ofNat]
    ring
  exact ⟨(hb t ht).1.trans_lt hp,
    (div_le_div_of_nonneg_right (hb t ht).2 (by norm_num)).trans_lt hv⟩

end GNC.OrbitalComparison
