import GNC.Applications.OrbitalComparison.PredictionBounds
import GNC.Analysis.FiniteAngleComparison
import GNC.Analysis.FundamentalSolution
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Comparison with a second-order state-transition Taylor approximation in
one constant pointing parameter. The quadratic gravity-Hessian response is
included in the comparator. Exact trigonometric forcing is also available to
classical methods; the result does not assert a coordinate-only advantage.
-/
noncomputable section
open Set GNC.FiniteAngleComparison
open scoped RealInnerProductSpace
namespace GNC.OrbitalComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A response is required to solve the actual retained physical ODE. -/
structure LinearResponse (q f : ℝ → E) where
  p : ℝ → E
  v : ℝ → E
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0 = 0
  initial_v : v 0 = 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt v ((360000:ℝ) • (Gravity.gradient mu (q t) (p t)+f t)) t

def gradientMap (q : E) : E →L[ℝ] E :=
  (3*mu/‖q‖^5) • (innerSL ℝ q).smulRight q-
    (mu/‖q‖^3) • ContinuousLinearMap.id ℝ E

theorem gradientMap_apply (q v : E) : gradientMap q v = Gravity.gradient mu q v := by
  simp only [gradientMap,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,innerSL_apply,Gravity.gradient]
  module

/-- The linear responses required in the comparison exist for every
continuous non-colliding reference and continuous forcing. -/
theorem LinearResponse.exists {q f : ℝ → E} (hq : Continuous q)
    (hq0 : ∀ t, q t ≠ 0) (hf : Continuous f) : Nonempty (LinearResponse q f) := by
  let A : ℝ → (E×E) →L[ℝ] (E×E) := fun t =>
    (ContinuousLinearMap.snd ℝ E E).prod
      ((360000:ℝ) • ((gradientMap (q t)).comp (ContinuousLinearMap.fst ℝ E E)))
  have hG : Continuous (fun t => gradientMap (q t)) := by
    unfold gradientMap
    fun_prop (disch := intro t; exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hq0 t)))
  have hA : Continuous A := by
    exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
      (continuous_const.prodMk (show Continuous (fun t => (360000:ℝ) •
        (gradientMap (q t)).comp (ContinuousLinearMap.fst ℝ E E)) by fun_prop))
  obtain ⟨x,hx,_⟩ := ForcedResponse.exists_unique_response A hA
    (fun t => ((0:E),(360000:ℝ) • f t)) (by fun_prop) (0:E×E)
  have hd := hx.2
  have hc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  refine ⟨⟨fun t => (x t).1,fun t => (x t).2,hc.fst,hc.snd,
    by simp [hx.1],by simp [hx.1],?_,?_⟩⟩
  · intro t _
    simpa [A] using (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t (hd t)
  · intro t _
    simpa [A,gradientMap_apply,smul_add] using
      (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t (hd t)


theorem gradient_combination (q u v : E) (a b : ℝ) :
    Gravity.gradient mu q (a • u+b • v) =
      a • Gravity.gradient mu q u+b • Gravity.gradient mu q v := by
  simp only [Gravity.gradient,inner_add_right,real_inner_smul_right]
  match_scalars <;> ring

def LinearResponse.combine {q f g : ℝ → E} (S : LinearResponse q f)
    (C : LinearResponse q g) (a b : ℝ) : LinearResponse q (fun t => a • f t+b • g t) where
  p := fun t => a • S.p t+b • C.p t
  v := fun t => a • S.v t+b • C.v t
  continuous_p := (S.continuous_p.const_smul a).add (C.continuous_p.const_smul b)
  continuous_v := (S.continuous_v.const_smul a).add (C.continuous_v.const_smul b)
  initial_p := by simp [S.initial_p,C.initial_p]
  initial_v := by simp [S.initial_v,C.initial_v]
  derivative_p := fun t ht => ((S.derivative_p t ht).const_smul a).add
    ((C.derivative_p t ht).const_smul b)
  derivative_v := fun t ht => by
    convert ((S.derivative_v t ht).const_smul a).add
      ((C.derivative_v t ht).const_smul b) using 1
    rw [gradient_combination]
    module

theorem LinearResponse.bound {q f : ℝ → E} (S : LinearResponse q f) {F : ℝ}
    (hF : 0 ≤ F) (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ≤ F) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖S.p t‖ ≤ (Direct.positionGain:ℝ)*360000*F := by
  have hb := response_gain S.p S.v
    (fun t => (360000:ℝ) • (Gravity.gradient mu (q t) (S.p t)+f t))
    (C := 360000*F) (by norm_num) (by positivity)
    S.continuous_p S.continuous_v S.derivative_p S.derivative_v S.initial_p S.initial_v (by
      intro t ht
      have hlin := gradient_normalized (q t) (S.p t) (hq t ht)
      have hin := hf t ht
      have hn := norm_add_le (Gravity.gradient mu (q t) (S.p t)) (f t)
      rw [norm_smul,Real.norm_eq_abs]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 360000)]
      linarith)
  intro t ht
  have h := (hb t ht).1
  rw [gain_values.1] at h
  nlinarith

/-- A convenient outward enclosure of a computed response bound. -/
theorem LinearResponse.column_bound {q f : ℝ → E} (S : LinearResponse q f)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ≤ (Direct.thrust:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖S.p t‖ < 3200 := by
  have hb := S.bound (by norm_num [Direct.thrust,Direct.gravityParameter,Direct.referenceRadius,Direct.angularSpeed]) hq hf
  intro t ht
  exact (hb t ht).trans_lt (by norm_num [Direct.positionGain,Direct.duration,Direct.pointingAngle,Direct.thrust,Direct.gravityParameter,Direct.referenceRadius,Direct.angularSpeed])

/-- The full second-order Taylor method has this extra Hessian forcing.
It is not replaced by an angle-only quadratic approximation. -/
def hessianForcing (q S : ℝ → E) (t : ℝ) : E :=
  (1/2:ℝ) • Gravity.hessian mu (q t) (S t) (S t)

/-- Differentiate the actual gravity field along a quadratic pointing jet. -/
theorem gravity_parameter_derivative (q S D : E) (a : ℝ)
    (hq : q+a • S+a^2 • D ≠ 0) :
    HasDerivAt (fun b => Gravity.field mu (q+b • S+b^2 • D))
      (Gravity.gradient mu (q+a • S+a^2 • D) S+
        (2*a) • Gravity.gradient mu (q+a • S+a^2 • D) D) a := by
  have hd : HasDerivAt (fun b : ℝ => q+b • S+b^2 • D) (S+(2*a) • D) a := by
    convert (((hasDerivAt_id a).smul_const S).const_add q).add
      (((hasDerivAt_id a).pow 2).smul_const D) using 1 <;> simp
  convert Gravity.field_derivative mu hd hq using 1
  simpa using (gradient_combination (q+a • S+a^2 • D) S D 1 (2*a)).symm

/-- The second derivative of the physical gravity along that jet includes
H[S,S] and 2 G D. This checks the forcing in the second variational equation. -/
theorem gravity_second_coefficient (q S D : E) (hq : q ≠ 0) :
    HasDerivAt (fun a : ℝ => Gravity.gradient mu (q+a • S+a^2 • D) S+
      (2*a) • Gravity.gradient mu (q+a • S+a^2 • D) D)
      (Gravity.hessian mu q S S+(2:ℝ) • Gravity.gradient mu q D) 0 := by
  have hd : HasDerivAt (fun b : ℝ => q+b • S+b^2 • D) S 0 := by
    convert (((hasDerivAt_id (0:ℝ)).smul_const S).const_add q).add
      (((hasDerivAt_id (0:ℝ)).pow 2).smul_const D) using 1 <;> simp
  have hz : q+(0:ℝ) • S+(0:ℝ)^2 • D ≠ 0 := by simpa using hq
  have hS := Gravity.gradient_derivative mu hd hz S
  have hD := Gravity.gradient_derivative mu hd hz D
  convert hS.add (((hasDerivAt_id (0:ℝ)).const_mul 2).smul hD) using 1 <;> simp

theorem hessian_response_bound {q fs : ℝ → E} (S : LinearResponse q fs)
    (Q : LinearResponse q (hessianForcing q S.p))
    (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ‖fs t‖ ≤ (Direct.thrust:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖Q.p t‖ < 1 := by
  have hS := S.column_bound hq hf
  have hforcing : ∀ t ∈ Icc (0:ℝ) 1,
      ‖hessianForcing q S.p t‖ ≤ 3*mu*3200^2/7000000^4 := by
    intro t ht
    have hqn : q t ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hq t ht))
    have hH := Gravity.hessian_bound mu (by norm_num [mu]) (q t) (S.p t) hqn
    have hden : 6*mu/‖q t‖^4 ≤ 6*mu/7000000^4 :=
      div_le_div_of_nonneg_left (by norm_num [mu]) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) (hq t ht) 4)
    have hb := hH.trans (mul_le_mul hden
      (pow_le_pow_left₀ (norm_nonneg _) (hS t ht).le 2) (sq_nonneg _) (by norm_num [mu]))
    rw [hessianForcing,norm_smul,Real.norm_eq_abs]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    nlinarith
  have hb := Q.bound (by norm_num [mu]) hq hforcing
  intro t ht
  exact (hb t ht).trans_lt (by norm_num [Direct.positionGain,mu])

/-- A strict comparison with an actual-error lower bound, not just a
comparison between two potentially loose error upper bounds. -/
theorem finite_angle_separation (p S C Q : E)
    (hS : (800:ℝ) ≤ ‖S‖) (hC : ‖C‖ ≤ 3200) (hQ : ‖Q‖ ≤ 1)
    (hp : ‖p-exactAngle (7/20) S C‖ < 117/1000) :
    2 < ‖p-taylorTwo (7/20) S C Q‖ ∧
      17*‖p-exactAngle (7/20) S C‖ < ‖p-taylorTwo (7/20) S C Q‖ := by
  let θ : ℝ := 7/20
  have hs := Real.sin_bound (x := θ) (by norm_num [θ])
  have hc := Real.cos_bound (x := θ) (by norm_num [θ])
  norm_num [θ] at hs hc
  have hs0 : 0 ≤ θ-Real.sin θ := by
    have hh := (abs_le.mp hs).2
    dsimp [θ]
    linarith
  have hbase := FiniteAngleComparison.error_lower θ p S C Q
  rw [abs_of_nonneg hs0] at hbase
  have hcos : |((1-Real.cos θ)-θ^2/2)| ≤ (θ^4)*(5/96) := by
    have heq : ((1-Real.cos θ)-θ^2/2) = -(Real.cos θ-(1-θ^2/2)) := by ring
    rw [heq,abs_neg]
    norm_num [θ]
    exact hc
  have hright := mul_le_mul hcos hC (norm_nonneg _) (by positivity : 0 ≤ θ^4*(5/96))
  have hq := mul_le_mul_of_nonneg_left hQ (sq_nonneg θ)
  have hleft := mul_le_mul_of_nonneg_left hS hs0
  have hslo := (abs_le.mp hs).2
  have hsep : 2 < ‖p-taylorTwo θ S C Q‖ := by
    dsimp [θ] at hbase hright hq hleft
    linarith
  refine ⟨hsep, ?_⟩
  have : 17*‖p-exactAngle θ S C‖ < 2 := by change _ < _ at hp; linarith
  exact this.trans hsep

/-- The conventional second-order predictor also gets a rigorous upper
certificate. Its width is computed from the same reference and response gain. -/
theorem second_order_certificate (p S C Q : E)
    (hS : ‖S‖ ≤ (Direct.positionGain:ℝ)*360000*(Direct.thrust:ℝ))
    (hC : ‖C‖ ≤ (Direct.positionGain:ℝ)*360000*(Direct.thrust:ℝ))
    (hQ : ‖Q‖ ≤ 1) (hp : ‖p-exactAngle (7/20) S C‖ < 117/1000) :
    ‖p-taylorTwo (7/20) S C Q‖ < 26 := by
  let θ : ℝ := 7/20
  have hs := Real.sin_bound (x := θ) (by norm_num [θ])
  have hc := Real.cos_bound (x := θ) (by norm_num [θ])
  have hsin : |θ-Real.sin θ| ≤ θ^3/6+θ^4*(5/96) := by
    have hh := abs_sub_le θ (θ-θ^3/6) (Real.sin θ)
    rw [abs_sub_comm (θ-θ^3/6) (Real.sin θ)] at hh
    norm_num [θ] at hs hh ⊢
    linarith
  have hcos : |1-Real.cos θ-θ^2/2| ≤ θ^4*(5/96) := by
    have he : 1-Real.cos θ-θ^2/2 = -(Real.cos θ-(1-θ^2/2)) := by ring
    rw [he,abs_neg]
    norm_num [θ] at hc ⊢
    exact hc
  have hb := FiniteAngleComparison.error_upper θ p S C Q
  have hsS := mul_le_mul hsin hS (norm_nonneg _) (by positivity : 0 ≤ θ^3/6+θ^4*(5/96))
  have hcC := mul_le_mul hcos hC (norm_nonneg _) (by positivity : 0 ≤ θ^4*(5/96))
  have hqQ := mul_le_mul_of_nonneg_left hQ (sq_nonneg θ)
  norm_num [θ,Direct.positionGain,Direct.thrust,Direct.gravityParameter,
    Direct.referenceRadius,Direct.angularSpeed] at hsS hcC hqQ hb
  linarith

/-- A physical thrust projection gives a nonzero endpoint sensitivity. The
gravity term is bounded using its actual derivative, not a sign assumption. -/
theorem LinearResponse.projected_lower {q f : ℝ → E} (S : LinearResponse q f)
    (w : E) (hw : ‖w‖ = 1)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖q t‖)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ≤ (Direct.thrust:ℝ))
    (hproj : ∀ t ∈ Icc (0:ℝ) 1, (12/1000:ℝ) ≤ ⟪w,f t⟫) :
    (800:ℝ) ≤ ‖S.p 1‖ := by
  have hS := S.column_bound hq hf
  have hacc (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (1600:ℝ) ≤ ⟪w,(360000:ℝ) • (Gravity.gradient mu (q t) (S.p t)+f t)⟫ := by
    have hlin := gradient_normalized (q t) (S.p t) (hq t ht)
    have hi := (abs_le.mp (abs_real_inner_le_norm w (Gravity.gradient mu (q t) (S.p t)))).1
    rw [hw,one_mul] at hi
    simp only [real_inner_smul_right,inner_add_right]
    have hp := hproj t ht
    have hs := hS t ht
    linarith
  have hv (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (1600:ℝ)*t ≤ ⟪w,S.v t⟫ := by
    have hb := image_le_of_deriv_right_le_deriv_boundary
      ((continuous_const.inner S.continuous_v).neg.continuousOn)
      (fun s hs => (((hasDerivAt_const s w).inner ℝ
        (S.derivative_v s (Ico_subset_Icc_self hs))).neg).hasDerivWithinAt)
      (B := fun s : ℝ => -1600*s) (B' := fun _ => -1600)
      (by simp [S.initial_v])
      (by fun_prop) (fun s _ => by
        simpa using ((hasDerivAt_id s).const_mul (-1600)).hasDerivWithinAt)
      (fun s hs => by simpa using neg_le_neg (hacc s (Ico_subset_Icc_self hs))) ht
    simpa using neg_le_neg hb
  have hb := image_le_of_deriv_right_le_deriv_boundary
    ((continuous_const.inner S.continuous_p).neg.continuousOn)
    (fun s hs => (((hasDerivAt_const s w).inner ℝ
      (S.derivative_p s (Ico_subset_Icc_self hs))).neg).hasDerivWithinAt)
    (B := fun s : ℝ => -800*s^2) (B' := fun s => -1600*s)
    (by simp [S.initial_p])
    (by fun_prop) (fun s _ => by
      convert (((hasDerivAt_id s).pow 2).const_mul (-800)).hasDerivWithinAt using 1 <;>
        simp only [id_eq] <;> ring)
    (fun s hs => by
      have hh := hv s (Ico_subset_Icc_self hs)
      simp only [inner_zero_left,zero_add]
      linarith) (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hi := real_inner_le_norm w (S.p 1)
  rw [hw,one_mul] at hi
  norm_num at hb
  linarith

end GNC.OrbitalComparison
