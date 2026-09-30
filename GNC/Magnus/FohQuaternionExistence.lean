import GNC.Magnus.FohCotangentFrame
import GNC.Magnus.FohRotationSolution

/-!
# Constructed quaternion families for the actual cotangent logarithm

Every affine angular input has a global quaternion solution initialized at
the identity. Noncommuting inputs use the existing Weber components in a
canonical SO(3) frame; commuting inputs use a quaternion exponential. The
Weber branch is packaged as units using the proved conserved quaternion norm.

The resulting centered-input family removes the quaternion-existence premise
from the first and second cotangent slope variations. The explicit SO(3)
frame specifies the continuous logarithm branch for `0 < θ < 2π`.
-/

noncomputable section
open Matrix NormedSpace Set Filter
open scoped Quaternion Matrix Matrix.Norms.Operator Topology
namespace GNC.Magnus

/-- Pure quaternion generator corresponding to an angular-rate vector. -/
def fohPureQuaternion (w : Vec3) : ℍ := fohQ 0 (w 0/2) (w 1/2) (w 2/2)

theorem foh_components_quaternion_ode (a : ℝ → ℝ) (v w : ℝ → Vec3)
    (ha : ∀ t, HasDerivAt a (-(v t ⬝ᵥ w t)/2) t)
    (hv : ∀ t, HasDerivAt v ((1/2 : ℝ) • (a t • w t + v t ⨯₃ w t)) t)
    (t : ℝ) :
    HasDerivAt (fun t => fohQ (a t) (v t 0) (v t 1) (v t 2))
      (fohQ (a t) (v t 0) (v t 1) (v t 2) * fohPureQuaternion (w t)) t := by
  convert fohQ_derivative (ha t) (hasDerivAt_pi.mp (hv t) 0)
    (hasDerivAt_pi.mp (hv t) 1) (hasDerivAt_pi.mp (hv t) 2) using 1
  ext <;> simp [fohPureQuaternion, fohQ, dotProduct, Fin.sum_univ_succ,
    cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem foh_components_quaternion_exists (a : ℝ → ℝ) (v w : ℝ → Vec3)
    (ha : ∀ t, HasDerivAt a (-(v t ⬝ᵥ w t)/2) t)
    (hv : ∀ t, HasDerivAt v ((1/2 : ℝ) • (a t • w t + v t ⨯₃ w t)) t)
    (ha0 : a 0 = 1) (hv0 : v 0 = 0) :
    ∃ q : ℝ → ℍˣ, q 0 = 1 ∧
      ∀ t, HasDerivAt (fun u => (q u).val) ((q t).val * fohPureQuaternion (w t)) t := by
  let p := fun t => fohQ (a t) (v t 0) (v t 1) (v t 2)
  have hn (t : ℝ) : Quaternion.normSq (p t) = 1 := by
    have hh := foh_quaternion_unit a v w ha hv ha0 hv0 t
    simpa [p, fohQ, Quaternion.normSq_def', lengthSq, add_assoc] using hh
  let q : ℝ → ℍˣ := fun t =>
    { val := p t
      inv := star (p t)
      val_inv := by rw [Quaternion.self_mul_star, hn]; rfl
      inv_val := by rw [Quaternion.star_mul_self, hn]; rfl }
  refine ⟨q, ?_, fun t => foh_components_quaternion_ode a v w ha hv t⟩
  apply Units.ext
  ext <;> simp [q, p, fohQ, ha0, hv0]

theorem foh_rotated_quaternion_exists (C : SO3) (a : ℝ → ℝ) (v w : ℝ → Vec3)
    (ha : ∀ t, HasDerivAt a (-(v t ⬝ᵥ w t)/2) t)
    (hv : ∀ t, HasDerivAt v ((1/2 : ℝ) • (a t • w t + v t ⨯₃ w t)) t)
    (ha0 : a 0 = 1) (hv0 : v 0 = 0) :
    ∃ q : ℝ → ℍˣ, q 0 = 1 ∧
      ∀ t, HasDerivAt (fun u => (q u).val)
        ((q t).val * fohPureQuaternion (rotate C (w t))) t := by
  apply foh_components_quaternion_exists a (fun t => rotate C (v t))
    (fun t => rotate C (w t))
  · simpa only [rotate_dot] using ha
  · intro t
    have hh := (Matrix.toLin' C.val).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hv t)
    change HasDerivAt (fun t => rotate C (v t))
      (rotate C ((1/2 : ℝ) • (a t • w t + v t ⨯₃ w t))) t at hh
    simpa only [rotate_smul, rotate_add, rotate_cross] using hh
  · exact ha0
  · simp [hv0]

local instance : NormedAlgebra ℚ ℍ := .restrictScalars ℚ ℝ ℍ

def fohQuaternionExpUnit (x : ℍ) : ℍˣ := (NormedSpace.isUnit_exp x).unit

@[simp] theorem fohQuaternionExpUnit_val (x : ℍ) :
    (fohQuaternionExpUnit x).val = exp x := (NormedSpace.isUnit_exp x).unit_spec

theorem foh_quaternion_fixed_axis_derivative (f : ℝ → ℝ) (u : Vec3) {t d : ℝ}
    (hf : HasDerivAt f d t) :
    HasDerivAt (fun s => (fohQuaternionExpUnit (f s • fohPureQuaternion u)).val)
      ((fohQuaternionExpUnit (f t • fohPureQuaternion u)).val * fohPureQuaternion (d • u)) t := by
  have hh := (hasDerivAt_exp_smul_const (fohPureQuaternion u) (f t)).scomp t hf
  convert hh using 1
  simp only [fohQuaternionExpUnit_val]
  have he : fohPureQuaternion (d • u) = d • fohPureQuaternion u := by
    ext <;> simp [fohPureQuaternion, fohQ] <;> ring
  rw [he, mul_smul_comm]

/-- Global affine quaternion solutions, including zero and commuting slopes. -/
theorem foh_affine_quaternion_exists (w s : Vec3) :
    ∃ q : ℝ → ℍˣ, q 0 = 1 ∧
      ∀ t, HasDerivAt (fun u => (q u).val)
        ((q t).val * fohPureQuaternion (w + t • s)) t := by
  by_cases hc : s ⨯₃ w = 0
  · by_cases hs : s = 0
    · subst s
      refine ⟨fun t => fohQuaternionExpUnit (t • fohPureQuaternion w), ?_, ?_⟩
      · apply Units.ext
        simp
      · intro t
        simpa using foh_quaternion_fixed_axis_derivative (fun t => t) w (hasDerivAt_id t)
    · let μ := (s ⬝ᵥ w) / (s ⬝ᵥ s)
      have hw : w = μ • s := foh_parallel_dependence w s hs hc
      let f : ℝ → ℝ := fun t => μ*t + t^2/2
      have hf (t : ℝ) : HasDerivAt f (μ + t) t := by
        convert ((hasDerivAt_id t).const_mul μ).add ((hasDerivAt_pow 2 t).div_const 2) using 1
        simp
      refine ⟨fun t => fohQuaternionExpUnit (f t • fohPureQuaternion s), ?_, ?_⟩
      · apply Units.ext
        simp [f]
      · intro t
        simpa only [hw, add_smul] using foh_quaternion_fixed_axis_derivative f s (hf t)
  · obtain ⟨C, δ, β, κ, hβ, hκ, hw, hs⟩ := foh_canonical_frame_exists w s hc
    obtain ⟨q, hq0, hqd⟩ := foh_rotated_quaternion_exists C
      (fohWeberQuaternionScalar (fohWeberAlpha β) δ β κ)
      (fohWeberQuaternionVector (fohWeberAlpha β) δ β κ)
      (fun t => ![κ, 0, δ + β*t])
      (fun t => (foh_weber_quaternion_ode _ _ _ _ t hβ.ne' hκ.ne' (foh_weberAlpha_sq hβ.le)).1)
      (fun t => (foh_weber_quaternion_ode _ _ _ _ t hβ.ne' hκ.ne' (foh_weberAlpha_sq hβ.le)).2)
      (foh_weber_quaternion_initial _ _ _ _ hβ.ne' hκ.ne' (foh_weberAlpha_sq hβ.le)).1
      (foh_weber_quaternion_initial _ _ _ _ hβ.ne' hκ.ne' (foh_weberAlpha_sq hβ.le)).2
    refine ⟨q, hq0, ?_⟩
    intro t
    have he : w + t • s = rotate C ![κ, 0, δ + β*t] := by
      rw [hw, hs]
      simp only [rotate, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
      congr 1
      ext i
      fin_cases i <;> simp
      ring
    rw [he]
    exact hqd t

def fohExactQuaternion (w s : Vec3) : ℝ → ℍˣ :=
  (foh_affine_quaternion_exists w s).choose

@[simp] theorem foh_exactQuaternion_initial (w s : Vec3) :
    fohExactQuaternion w s 0 = 1 :=
  (foh_affine_quaternion_exists w s).choose_spec.1

theorem foh_exactQuaternion_derivative (w s : Vec3) (t : ℝ) :
    HasDerivAt (fun u => (fohExactQuaternion w s u).val)
      ((fohExactQuaternion w s t).val * fohPureQuaternion (w + t • s)) t :=
  (foh_affine_quaternion_exists w s).choose_spec.2 t

/-- A constructed global quaternion family for the canonical centered input. -/
def fohCotQuaternionFamily (θ u v e : ℝ) : ℝ → ℍˣ :=
  fohExactQuaternion (![0, 0, θ] - (e/2) • (![u, 0, v] : Vec3))
    (e • (![u, 0, v] : Vec3))

@[simp] theorem foh_cotQuaternionFamily_initial (θ u v e : ℝ) :
    fohCotQuaternionFamily θ u v e 0 = 1 := foh_exactQuaternion_initial _ _

theorem foh_cotQuaternionFamily_derivative (θ u v e t : ℝ) :
    HasDerivAt (fun s => (fohCotQuaternionFamily θ u v e s).val)
      ((fohCotQuaternionFamily θ u v e t).val *
        (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t := by
  convert foh_exactQuaternion_derivative
    (![0, 0, θ] - (e/2) • (![u, 0, v] : Vec3)) (e • (![u, 0, v] : Vec3)) t using 1
  congr 1
  ext <;> simp [fohPureQuaternion, fohQuaternionSlopeInput, fohQ] <;> ring

/-- The actual cotangent logarithm and both variations, with the canonical
quaternion family constructed rather than assumed. The only solution supplied
by the caller is the physical rotation family obeying its original time ODE. -/
theorem foh_cot_frame_constructed_log (C : SO3) (F G : Vec3)
    {θ : ℝ} (hθ : 0 < θ) (hπ : θ < 2*Real.pi) (u v : ℝ)
    (hF : F = rotate C ![0,0,θ]) (hG : G = rotate C ![u,0,v])
    (R : ℝ → ℝ → SO3)
    (hR : ∀ e t, HasDerivAt (fun s => (R e s).val)
      ((R e t).val * skew (F + e • ((t-1/2) • G))) t)
    (hR0 : ∀ e, R e 0 = 1) :
    let φ := fun e => fohFrameQuaternionLog C (fohCotQuaternionFamily θ u v e 1).val
    φ 0 = F ∧
    (∀ᶠ e in 𝓝 (0 : ℝ), rotationExp (φ e) = R e 1) ∧
    HasDerivAt φ (fohCotC θ • (F ⨯₃ G)) 0 ∧
    Tendsto (fun e : ℝ => (e^2)⁻¹ • (φ e - F - e • (fohCotC θ • (F ⨯₃ G))))
      (𝓝[≠] 0) (𝓝 ((fohCotAlpha θ*lengthSq G+fohCotGamma θ*(F ⬝ᵥ G)^2) • F +
        (fohCotBeta θ*(F ⬝ᵥ G)) • G)) :=
  foh_cot_frame_actual_log C F G hθ hπ u v hF hG (fohCotQuaternionFamily θ u v) R
    (foh_cotQuaternionFamily_derivative θ u v) (foh_cotQuaternionFamily_initial θ u v)
    hR hR0

end GNC.Magnus
