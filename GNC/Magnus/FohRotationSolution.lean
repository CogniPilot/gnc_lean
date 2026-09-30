import GNC.Magnus.FohCanonicalFrame
import GNC.Magnus.FohRotationSensitivity

/-! Actual global FOH rotation solutions, including commuting inputs. This
provides the parameterized solution families needed by sensitivity, rather
than leaving their existence as a premise. -/
noncomputable section
open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Magnus

theorem foh_fixed_axis_derivative (f : ℝ → ℝ) (u : Vec3) {t d : ℝ}
    (hf : HasDerivAt f d t) :
    HasDerivAt (fun s => (rotationExp (f s • u)).val)
      ((rotationExp (f t • u)).val * skew (d • u)) t := by
  have h := (hasDerivAt_exp_smul_const (skew u) (f t)).scomp t hf
  convert h using 1
  · simp only [rotationExp, skew_smul, Function.comp_def]
  · simp only [rotationExp, skew_smul, smul_mul_assoc, mul_smul_comm]

theorem foh_rotationExp_zero : rotationExp 0 = 1 := by
  apply Subtype.ext
  change exp (Cayley.skewLinear 0) = 1
  rw [map_zero, exp_zero]

theorem foh_parallel_dependence (w s : Vec3) (hs : s ≠ 0) (hc : s ⨯₃ w = 0) :
    w = ((s ⬝ᵥ w) / (s ⬝ᵥ s)) • s := by
  have hn : s ⬝ᵥ s ≠ 0 := by
    rw [dot_self_lengthSq]
    exact (lengthSq_eq_zero_iff s).not.mpr hs
  have h : (s ⬝ᵥ w) • s - (s ⬝ᵥ s) • w = 0 := by
    rw [← cross_cross_eq_smul_sub_smul', hc]
    simp
  have he := congrArg (fun v : Vec3 => (s ⬝ᵥ s)⁻¹ • v) (sub_eq_zero.mp h)
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul, div_eq_mul_inv, mul_comm] using he.symm

/-- Every real affine angular rate has an actual global SO(3) solution.
The generic branch is Weber; commuting branches use a single exponential. -/
theorem foh_affine_rotation_exists (w s : Vec3) :
    ∃ R : ℝ → SO3, R 0 = 1 ∧
      ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew (w + t • s)) t := by
  by_cases hc : s ⨯₃ w = 0
  · by_cases hs : s = 0
    · subst s
      refine ⟨fun t => rotationExp (t • w), ?_, ?_⟩
      · simpa using foh_rotationExp_zero
      · intro t
        simpa using foh_fixed_axis_derivative (fun t => t) w (hasDerivAt_id t)
    · let μ := (s ⬝ᵥ w) / (s ⬝ᵥ s)
      have hw : w = μ • s := foh_parallel_dependence w s hs hc
      let f : ℝ → ℝ := fun t => μ * t + t ^ 2 / 2
      have hf (t : ℝ) : HasDerivAt f (μ + t) t := by
        convert ((hasDerivAt_id t).const_mul μ).add ((hasDerivAt_pow 2 t).div_const 2) using 1
        simp
      refine ⟨fun t => rotationExp (f t • s), ?_, ?_⟩
      · simpa [f] using foh_rotationExp_zero
      · intro t
        simpa only [hw, add_smul] using foh_fixed_axis_derivative f s (hf t)
  · obtain ⟨C, δ, β, κ, hβ, hκ, hw, hs⟩ := foh_canonical_frame_exists w s hc
    obtain ⟨S, hs0, _, hsd⟩ := foh_weber_to_rotation (fohWeberAlpha β) δ β κ
      hβ.ne' hκ.ne' (foh_weberAlpha_sq hβ.le)
    refine ⟨fun t => C * S t * C⁻¹, by simp [hs0], ?_⟩
    intro t
    have he : w + t • s = rotate C ![κ, 0, δ + β * t] := by
      rw [hw, hs]
      simp only [rotate, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
      congr 1
      ext i
      fin_cases i <;> simp <;> ring
    rw [he]
    exact foh_conjugate_rotation_derivative C S _ (hsd t)

def fohExactRotation (w s : Vec3) : ℝ → SO3 := (foh_affine_rotation_exists w s).choose

@[simp] theorem foh_exactRotation_initial (w s : Vec3) : fohExactRotation w s 0 = 1 :=
  (foh_affine_rotation_exists w s).choose_spec.1

theorem foh_exactRotation_derivative (w s : Vec3) (t : ℝ) :
    HasDerivAt (fun u => (fohExactRotation w s u).val)
      ((fohExactRotation w s t).val * skew (w + t • s)) t :=
  (foh_affine_rotation_exists w s).choose_spec.2 t

theorem foh_exactRotation_unique (R : ℝ → SO3) (w s : Vec3)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew (w + t • s)) t)
    (hR0 : R 0 = 1) : R = fohExactRotation w s :=
  foh_rotation_ode_unique R (fohExactRotation w s) (fun t => w + t • s) hR
    (foh_exactRotation_derivative w s) (hR0.trans (foh_exactRotation_initial w s).symm)

/-- Zeroth moment of the actual, constructed solution as a genuine
derivative with respect to the constant angular-rate vector. -/
theorem foh_exactRotation_constant_sensitivity (w s x : Vec3) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q : ℝ => (fohExactRotation (w + q • x) s T).val * (fohExactRotation w s T)⁻¹.val)
      (skew (∫ t in (0 : ℝ)..T, rotate (fohExactRotation w s t) x)) 0 := by
  have hd := foh_constant_rate_sensitivity
    (fun q => fohExactRotation (w + q • x) s) w s x
    (fun q t => by
      convert foh_exactRotation_derivative (w + q • x) s t using 1
      congr 2
      module)
    (fun q => foh_exactRotation_initial _ _) hT
  simpa only [zero_smul, add_zero] using hd

/-- First moment as the genuine angular-slope derivative of the same
constructed FOH solution. -/
theorem foh_exactRotation_linear_sensitivity (w s x : Vec3) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q : ℝ => (fohExactRotation w (s + q • x) T).val * (fohExactRotation w s T)⁻¹.val)
      (skew (∫ t in (0 : ℝ)..T, t • rotate (fohExactRotation w s t) x)) 0 := by
  have hd := foh_linear_rate_sensitivity
    (fun q => fohExactRotation w (s + q • x)) w s x
    (fun q t => foh_exactRotation_derivative w (s + q • x) t)
    (fun q => foh_exactRotation_initial _ _) hT
  simpa only [zero_smul, add_zero] using hd

end GNC.Magnus
