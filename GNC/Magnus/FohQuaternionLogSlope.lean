import GNC.Magnus.FohQuaternionSlope
import GNC.Magnus.FohQuaternionRotation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual quadratic slope expansion in the local quaternion
rotation-vector chart. The chart is defined explicitly, and its scalar
composition is justified by differentiability, including paths whose
scalar component equals its base value at arbitrarily many points. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology Quaternion
namespace GNC.Magnus

/-- A quadratic scalar variation composes with an ordinary first derivative.
No nonvanishing assumption on the scalar increment is needed. -/
theorem foh_scaled_scalar_composition {ι : Type*} {l : Filter ι}
    (a r : ι → ℝ) (h : ℝ → ℝ) (a₀ a₂ dh : ℝ)
    (ha : Tendsto a l (𝓝 a₀))
    (ha₂ : Tendsto (fun e => r e * (a e - a₀)) l (𝓝 a₂))
    (hh : HasDerivAt h dh a₀) :
    Tendsto (fun e => r e * (h (a e) - h a₀)) l (𝓝 (dh * a₂)) := by
  let D := Function.update (fun x => (h x - h a₀) / (x-a₀)) a₀ dh
  have hd : Tendsto (fun e => D (a e)) l (𝓝 dh) := by
    simpa [D] using hh.continuousAt_div.tendsto.comp ha
  have he (x : ℝ) : D x * (x-a₀) = h x - h a₀ := by
    by_cases hx : x = a₀
    · simp [hx]
    · simp [D, Function.update_of_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]
  apply (hd.mul ha₂).congr
  intro e
  change D (a e) * (r e * (a e-a₀)) = r e * (h (a e)-h a₀)
  rw [← mul_assoc, mul_comm (D (a e)), mul_assoc, he]

/-- Product rule for a second variation whose scalar factor has no linear
term. The scalar quadratic contribution multiplies the base vector. -/
theorem foh_scaled_vector_product {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter ι} (r e h : ι → ℝ) (w : ι → V) (h₀ h₂ : ℝ) (w₀ w₁ w₂ : V)
    (hw : Tendsto w l (𝓝 w₀))
    (hh : Tendsto (fun x => r x * (h x-h₀)) l (𝓝 h₂))
    (hw₂ : Tendsto (fun x => r x • (w x-w₀-e x • w₁)) l (𝓝 w₂)) :
    Tendsto (fun x => r x • (h x • w x-h₀ • w₀-e x • (h₀ • w₁))) l
      (𝓝 (h₀ • w₂ + h₂ • w₀)) := by
  apply ((tendsto_const_nhds.smul hw₂).add (hh.smul hw)).congr
  intro x
  module

def fohQuaternionLogScale (a : ℝ) : ℝ :=
  2 * Real.arccos a / Real.sqrt (1-a^2)

/-- Twice the imaginary quaternion logarithm on the unit-quaternion chart
away from the real poles. Values are pure quaternions (three coordinates). -/
def fohQuaternionRotationVector (q : ℍ) : ℍ :=
  fohQuaternionLogScale q.re • q.im

theorem fohQuaternionLogScale_at {θ : ℝ} (hθ : 0 < θ) (hπ : θ < 2*Real.pi) :
    fohQuaternionLogScale (Real.cos (θ/2)) = θ / Real.sin (θ/2) ∧
    HasDerivAt fohQuaternionLogScale
      (θ * Real.cos (θ/2) / Real.sin (θ/2)^3 - 2 / Real.sin (θ/2)^2)
      (Real.cos (θ/2)) := by
  have hp : 0 < θ/2 := by linarith
  have hl : θ/2 < Real.pi := by linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi hp hl
  have hsq : 1-Real.cos (θ/2)^2 = Real.sin (θ/2)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  have hr : Real.sqrt (1-Real.cos (θ/2)^2) = Real.sin (θ/2) := by
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hs]
  have hc := Real.arccos_cos hp.le hl.le
  have hm : Real.cos (θ/2) ≠ -1 := by
    intro h
    rw [h] at hsq
    nlinarith [sq_pos_of_pos hs]
  have hn : Real.cos (θ/2) ≠ 1 := by
    intro h
    rw [h] at hsq
    nlinarith [sq_pos_of_pos hs]
  constructor
  · simp [fohQuaternionLogScale, hc, hr]
    ring
  · have hd := ((Real.hasDerivAt_arccos hm hn).const_mul 2).div
      ((((hasDerivAt_id (Real.cos (θ/2))).pow 2).const_sub 1).sqrt
        (by dsimp; rw [hsq]; positivity)) (by dsimp; rw [hr]; exact ne_of_gt hs)
    convert hd using 1
    dsimp
    rw [hr, hc]
    field_simp
    <;> ring

/-- Explicit second-variation chain rule for the rotation-vector chart. -/
theorem fohQuaternionRotationVector_second_limit (q : ℝ → ℍ) (q₀ q₁ q₂ : ℍ)
    (dh : ℝ) (hq : Tendsto q (𝓝[≠] 0) (𝓝 q₀)) (hre : q₁.re = 0)
    (h₂ : Tendsto (fun e : ℝ => (e^2)⁻¹ • (q e-q₀-e • q₁))
      (𝓝[≠] 0) (𝓝 q₂))
    (hh : HasDerivAt fohQuaternionLogScale dh q₀.re) :
    Tendsto (fun e : ℝ => (e^2)⁻¹ •
      (fohQuaternionRotationVector (q e)-fohQuaternionRotationVector q₀-
        e • (fohQuaternionLogScale q₀.re • q₁.im)))
      (𝓝[≠] 0)
      (𝓝 (fohQuaternionLogScale q₀.re • q₂.im + (dh*q₂.re) • q₀.im)) := by
  have ha := Quaternion.continuous_re.continuousAt.tendsto.comp hq
  have hw := Quaternion.continuous_im.continuousAt.tendsto.comp hq
  have ha₂ : Tendsto (fun e : ℝ => (e^2)⁻¹ * ((q e).re-q₀.re))
      (𝓝[≠] 0) (𝓝 q₂.re) := by
    simpa [Function.comp_def, Quaternion.re_sub, Quaternion.re_smul, hre] using
      Quaternion.continuous_re.continuousAt.tendsto.comp h₂
  have hw₂ : Tendsto (fun e : ℝ => (e^2)⁻¹ • ((q e).im-q₀.im-e • q₁.im))
      (𝓝[≠] 0) (𝓝 q₂.im) := by
    simpa only [Function.comp_def, Quaternion.im_sub, Quaternion.im_smul] using
      Quaternion.continuous_im.continuousAt.tendsto.comp h₂
  exact foh_scaled_vector_product (fun e : ℝ => (e^2)⁻¹) id
    (fun e => fohQuaternionLogScale (q e).re) (fun e => (q e).im)
    (fohQuaternionLogScale q₀.re) (dh*q₂.re) q₀.im q₁.im q₂.im hw
    (foh_scaled_scalar_composition (fun e => (q e).re) (fun e : ℝ => (e^2)⁻¹)
      fohQuaternionLogScale q₀.re q₂.re dh ha ha₂ hh) hw₂

/-- Algebraic first and second coefficients after the quaternion chart
chain rule, with the scalar contribution included. -/
theorem fohQuaternionLog_cot_coefficients {θ : ℝ} (hθ : 0 < θ)
    (hπ : θ < 2*Real.pi) (u v : ℝ) :
    fohQuaternionRotationVector (fohMeanQuaternion θ 1).val = fohQ 0 0 0 θ ∧
    fohQuaternionLogScale (fohMeanQuaternion θ 1).val.re •
      (fohQuaternionSlopeFirst θ u).im = fohQ 0 0 (θ*u*fohCotC θ) 0 ∧
    fohQuaternionLogScale (fohMeanQuaternion θ 1).val.re •
      (fohQuaternionSlopeSecond θ u v).im +
      ((θ*Real.cos (θ/2)/Real.sin (θ/2)^3-2/Real.sin (θ/2)^2)*
        (fohQuaternionSlopeSecond θ u v).re) • (fohMeanQuaternion θ 1).val.im =
      fohQ 0 (θ*u*v*fohCotBeta θ) 0 (θ*u^2*fohCotAlpha θ) := by
  have hs : Real.sin (θ/2) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hc := (fohQuaternionLogScale_at hθ hπ).1
  constructor
  · ext <;> simp [fohQuaternionRotationVector, fohMeanQuaternion, fohQ, hc] <;>
      field_simp <;> ring
  constructor
  · ext <;> simp [fohMeanQuaternion, fohQuaternionSlopeFirst, fohQ, hc] <;>
      field_simp <;> ring
  · ext <;> simp [fohMeanQuaternion, fohQuaternionSlopeSecond, fohQ, hc, fohCotAlpha] <;>
      field_simp <;> ring

/-- Actual affine-slope flow has the quadratic cotangent coefficient in
the local rotation-vector chart. This is a limit of the actual flow, not
an assumed or fitted logarithm series. The chart range is `0 < θ < 2π`. -/
theorem fohQuaternion_actual_log_cot_second {θ : ℝ} (hθ : 0 < θ)
    (hπ : θ < 2*Real.pi) (u v : ℝ) (R : ℝ → ℝ → ℍˣ)
    (hR : ∀ e t, HasDerivAt (fun s => (R e s).val)
      ((R e t).val * (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t)
    (hR0 : ∀ e, R e 0 = 1) :
    Tendsto (fun e : ℝ => (e^2)⁻¹ •
      (fohQuaternionRotationVector (R e 1).val - fohQ 0 0 0 θ -
        e • fohQ 0 0 (θ*u*fohCotC θ) 0))
      (𝓝[≠] 0) (𝓝 (fohQ 0 (θ*u*v*fohCotBeta θ) 0 (θ*u^2*fohCotAlpha θ))) := by
  have hs : Real.sin (θ/2) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hv := foh_actual_slope_variations (fun _ => fohQ 0 0 0 (θ/2))
    (fohQuaternionSlopeInput u v) R continuous_const
    (fohQuaternionSlopeInput_continuous u v) hR hR0 (by norm_num : (0:ℝ) ≤ 1)
  rw [fohQuaternion_actual_base θ u v R hR hR0,
    fohQuaternion_first_endpoint hθ.ne' hs, fohQuaternion_second_endpoint_cot hθ.ne' hs] at hv
  have hq : Tendsto (fun e => (R e 1).val) (𝓝[≠] 0) (𝓝 (fohMeanQuaternion θ 1).val) := by
    have hc := hv.1.continuousAt.tendsto.mono_left
      (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    rwa [fohQuaternion_actual_base θ u v R hR hR0] at hc
  have hh := fohQuaternionRotationVector_second_limit (fun e => (R e 1).val)
    (fohMeanQuaternion θ 1).val (fohQuaternionSlopeFirst θ u) (fohQuaternionSlopeSecond θ u v)
    _ hq (by rfl) hv.2 (by simpa [fohMeanQuaternion, fohQ] using (fohQuaternionLogScale_at hθ hπ).2)
  obtain ⟨ha,hb,hc⟩ := fohQuaternionLog_cot_coefficients hθ hπ u v
  rwa [ha, hb, hc] at hh

def fohQuaternionReCLM : ℍ →L[ℝ] ℝ :=
  ⟨QuaternionAlgebra.reₗ (-1) 0 (-1), Quaternion.continuous_re⟩

def fohQuaternionImCLM : ℍ →L[ℝ] ℍ where
  toFun := QuaternionAlgebra.im
  map_add' := Quaternion.im_add
  map_smul' r q := Quaternion.im_smul q r
  cont := Quaternion.continuous_im

theorem fohQuaternionRotationVector_hasDerivAt {q : ℝ → ℍ} {q' : ℍ} {t dh : ℝ}
    (hq : HasDerivAt q q' t) (hre : q'.re = 0)
    (hh : HasDerivAt fohQuaternionLogScale dh (q t).re) :
    HasDerivAt (fun e => fohQuaternionRotationVector (q e))
      (fohQuaternionLogScale (q t).re • q'.im) t := by
  have ha := fohQuaternionReCLM.hasFDerivAt.comp_hasDerivAt t hq
  have hw := fohQuaternionImCLM.hasFDerivAt.comp_hasDerivAt t hq
  change HasDerivAt (fun e => (q e).re) q'.re t at ha
  change HasDerivAt (fun e => (q e).im) q'.im t at hw
  have hs := (hh.comp t ha).smul hw
  simpa [fohQuaternionRotationVector, Function.comp_def, Pi.smul_apply, hre] using hs

/-- The actual first slope derivative in the same rotation-vector chart. -/
theorem fohQuaternion_actual_log_cot_first {θ : ℝ} (hθ : 0 < θ)
    (hπ : θ < 2*Real.pi) (u v : ℝ) (R : ℝ → ℝ → ℍˣ)
    (hR : ∀ e t, HasDerivAt (fun s => (R e s).val)
      ((R e t).val * (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t)
    (hR0 : ∀ e, R e 0 = 1) :
    HasDerivAt (fun e => fohQuaternionRotationVector (R e 1).val)
      (fohQ 0 0 (θ*u*fohCotC θ) 0) 0 := by
  have hs : Real.sin (θ/2) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hv := foh_parameter_integral_hasDerivAt (fun _ => fohQ 0 0 0 (θ/2))
    (fohQuaternionSlopeInput u v) R continuous_const
    (fohQuaternionSlopeInput_continuous u v) hR hR0 (by norm_num : (0:ℝ) ≤ 1)
  rw [fohQuaternion_actual_base θ u v R hR hR0, fohQuaternion_first_endpoint hθ.ne' hs] at hv
  have hbase : (R 0 1).val = (fohMeanQuaternion θ 1).val := by
    rw [fohQuaternion_actual_base θ u v R hR hR0]
  have hh := fohQuaternionRotationVector_hasDerivAt hv (by rfl)
    (by rw [hbase]; simpa [fohMeanQuaternion, fohQ] using (fohQuaternionLogScale_at hθ hπ).2)
  rw [hbase] at hh
  exact hh.congr_deriv (fohQuaternionLog_cot_coefficients hθ hπ u v).2.1

/-- The canonical quadratic vector coefficient is exactly the invariant
three-coefficient expression. The parallel-slope contributions cancel. -/
theorem fohQuaternion_log_invariant_quadratic {θ : ℝ} (hθ : θ ≠ 0) (u v : ℝ) :
    (fohCotAlpha θ*(u^2+v^2)+fohCotGamma θ*(θ*v)^2) • fohQ 0 0 0 θ +
      (fohCotBeta θ*(θ*v)) • fohQ 0 u 0 v =
      fohQ 0 (θ*u*v*fohCotBeta θ) 0 (θ*u^2*fohCotAlpha θ) := by
  have hc := fohCot_quadratic_commuting hθ
  ext <;> simp [fohQ]
  · ring
  · nlinarith [congrArg (fun r : ℝ => θ*v^2*r) hc]

/-- The actual quaternion time ODE preserves unit norm. This follows from
the component derivatives and initialization, not from membership in `Units`. -/
theorem fohQuaternion_actual_normSq (θ u v : ℝ) (R : ℝ → ℝ → ℍˣ)
    (hR : ∀ e t, HasDerivAt (fun s => (R e s).val)
      ((R e t).val * (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t)
    (hR0 : ∀ e, R e 0 = 1) (e t : ℝ) : Quaternion.normSq (R e t).val = 1 := by
  let Li : ℍ →L[ℝ] ℝ := ⟨QuaternionAlgebra.imIₗ (-1) 0 (-1), Quaternion.continuous_imI⟩
  let Lj : ℍ →L[ℝ] ℝ := ⟨QuaternionAlgebra.imJₗ (-1) 0 (-1), Quaternion.continuous_imJ⟩
  let Lk : ℍ →L[ℝ] ℝ := ⟨QuaternionAlgebra.imKₗ (-1) 0 (-1), Quaternion.continuous_imK⟩
  have hd (s : ℝ) : HasDerivAt (fun s => Quaternion.normSq (R e s).val) 0 s := by
    have ha := fohQuaternionReCLM.hasFDerivAt.comp_hasDerivAt s (hR e s)
    have hi := Li.hasFDerivAt.comp_hasDerivAt s (hR e s)
    have hj := Lj.hasFDerivAt.comp_hasDerivAt s (hR e s)
    have hk := Lk.hasFDerivAt.comp_hasDerivAt s (hR e s)
    change HasDerivAt (fun x => (R e x).val.re)
      ((R e s).val * (fohQ 0 0 0 (θ/2)+e • fohQuaternionSlopeInput u v s)).re s at ha
    change HasDerivAt (fun x => (R e x).val.imI)
      ((R e s).val * (fohQ 0 0 0 (θ/2)+e • fohQuaternionSlopeInput u v s)).imI s at hi
    change HasDerivAt (fun x => (R e x).val.imJ)
      ((R e s).val * (fohQ 0 0 0 (θ/2)+e • fohQuaternionSlopeInput u v s)).imJ s at hj
    change HasDerivAt (fun x => (R e x).val.imK)
      ((R e s).val * (fohQ 0 0 0 (θ/2)+e • fohQuaternionSlopeInput u v s)).imK s at hk
    convert (((ha.pow 2).add (hi.pow 2)).add (hj.pow 2)).add (hk.pow 2) using 1
    · funext x
      simp [Quaternion.normSq_def', fohQuaternionReCLM, Li, Lj, Lk, Function.comp_def,
        QuaternionAlgebra.reₗ, QuaternionAlgebra.imIₗ, QuaternionAlgebra.imJₗ, QuaternionAlgebra.imKₗ]
    · simp [fohQuaternionReCLM, Li, Lj, Lk, fohQ, fohQuaternionSlopeInput,
        QuaternionAlgebra.reₗ, QuaternionAlgebra.imIₗ, QuaternionAlgebra.imJₗ, QuaternionAlgebra.imKₗ]
      ring
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa [hR0] using h

/-- Direct axis-angle reconstruction from the explicit chart. Thus the
chart used in the variation theorem really recovers the unit quaternion. -/
theorem fohQuaternion_rotationVector_reconstruct (q : ℍ)
    (hn : Quaternion.normSq q = 1) (ha : -1 < q.re) (hb : q.re < 1) :
    q = Real.cos (‖fohQuaternionRotationVector q‖/2) • (1 : ℍ) +
      (Real.sin (‖fohQuaternionRotationVector q‖/2)/‖fohQuaternionRotationVector q‖) •
        fohQuaternionRotationVector q := by
  have hsq : 0 < 1-q.re^2 := by nlinarith
  have hr : 0 < Real.sqrt (1-q.re^2) := Real.sqrt_pos.mpr hsq
  have hac : 0 < Real.arccos q.re := Real.arccos_pos.mpr hb
  have hi : ‖q.im‖ = Real.sqrt (1-q.re^2) := by
    rw [norm_eq_sqrt_real_inner, Quaternion.inner_self]
    congr 1
    simp [Quaternion.normSq_def'] at hn ⊢
    linarith
  have hl : 0 < fohQuaternionLogScale q.re := by
    unfold fohQuaternionLogScale
    positivity
  have hnorm : ‖fohQuaternionRotationVector q‖ = 2*Real.arccos q.re := by
    rw [fohQuaternionRotationVector, norm_smul, Real.norm_eq_abs, abs_of_pos hl, hi]
    unfold fohQuaternionLogScale
    field_simp
  have hhalf : ‖fohQuaternionRotationVector q‖/2 = Real.arccos q.re := by rw [hnorm]; ring
  rw [hhalf, Real.cos_arccos ha.le hb.le, Real.sin_arccos, hnorm]
  ext <;> simp [fohQuaternionRotationVector, fohQuaternionLogScale]
  all_goals field_simp
  all_goals ring

/-- Three-vector form of the canonical quadratic coefficient. -/
theorem foh_log_canonical_quadratic_vec {θ : ℝ} (hθ : θ ≠ 0) (u v : ℝ) :
    (fohCotAlpha θ * lengthSq (![u,0,v] : Vec3) +
      fohCotGamma θ * ((![0,0,θ] : Vec3) ⬝ᵥ (![u,0,v] : Vec3))^2) • (![0,0,θ] : Vec3) +
    (fohCotBeta θ * ((![0,0,θ] : Vec3) ⬝ᵥ (![u,0,v] : Vec3))) • (![u,0,v] : Vec3) =
      ![θ*u*v*fohCotBeta θ, 0, θ*u^2*fohCotAlpha θ] := by
  have hc := fohCot_quadratic_commuting hθ
  ext i
  fin_cases i <;> simp [lengthSq, dotProduct, Fin.sum_univ_succ]
  · ring
  · nlinarith [congrArg (fun r : ℝ => θ*v^2*r) hc]

/-- The invariant quadratic expression commutes with every SO(3) frame
change; no coordinate convention enters its scalar coefficients. -/
theorem foh_log_quadratic_rotation_equivariant (θ : ℝ) (R : SO3) (F G : Vec3) :
    (fohCotAlpha θ*lengthSq (rotate R G)+
      fohCotGamma θ*(rotate R F ⬝ᵥ rotate R G)^2) • rotate R F +
      (fohCotBeta θ*(rotate R F ⬝ᵥ rotate R G)) • rotate R G =
    rotate R ((fohCotAlpha θ*lengthSq G+fohCotGamma θ*(F ⬝ᵥ G)^2) • F +
      (fohCotBeta θ*(F ⬝ᵥ G)) • G) := by
  simp [rotate_lengthSq, rotate_dot, rotate_smul]

end GNC.Magnus
