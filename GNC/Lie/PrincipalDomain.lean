import GNC.Lie.PrincipalLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Characterization of the principal logarithm domain through the Cayley
chart and absence of the rotation eigenvalue -1. -/
noncomputable section
open Matrix Real Set
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Cayley

theorem matrix_closed (q : Vec3) :
    matrix q = 1+(2/(1+enorm q^2)) • skew q+(2/(1+enorm q^2)) • skew q^2 := by
  let c := 2/(1+enorm q^2)
  have hc : c*(1+enorm q^2) = 2 := by dsimp [c]; field_simp
  have hp : (1+c • skew q+c • skew q^2)*minus q = plus q := by
    unfold minus plus
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, ← pow_succ, ← pow_two]
    rw [skew_cube, smul_smul]
    have hc' : c-1+c*enorm q^2 = 1 := by nlinarith only [hc]
    linear_combination (norm := module) hc' • skew q
  calc
    matrix q = ((1+c • skew q+c • skew q^2)*minus q)*(minus q)⁻¹ := by rw [hp]; rfl
    _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (minus_unit q), Matrix.mul_one]

theorem rotationExp_axis (k : Vec3) (hk : k ⬝ᵥ k = 1) (θ : ℝ) (hθ : 0 < θ) :
    (rotationExp (θ • k)).val = 1+sin θ • skew k+(1-cos θ) • skew k^2 := by
  have hn : enorm (θ • k) = θ := by simp [enorm_smul, Gravity.unit_enorm k hk, abs_of_pos hθ]
  rw [rotationExp_formula, hn, skew_smul, smul_pow, smul_smul, smul_smul]
  congr 2 <;> field_simp

theorem matrix_axis (k : Vec3) (hk : k ⬝ᵥ k = 1) (s : ℝ) :
    matrix (s • k) = 1+(2*s/(1+s^2)) • skew k+(2*s^2/(1+s^2)) • skew k^2 := by
  rw [matrix_closed, enorm_smul, Gravity.unit_enorm k hk, mul_one, sq_abs,
    skew_smul, smul_pow, smul_smul, smul_smul]
  congr 2 <;> ring

theorem rotation_axis_tan (k : Vec3) (hk : k ⬝ᵥ k = 1) (θ : ℝ)
    (hθ : 0 < θ) (hθπ : θ < π) : rotation ((tan (θ/2)) • k) = rotationExp (θ • k) := by
  have hc : cos (θ/2) ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],by linarith⟩).ne'
  have hs : sin θ = 2*sin (θ/2)*cos (θ/2) := by
    convert sin_two_mul (θ/2) using 1; congr 1; ring
  have hh : cos θ = 1-2*sin (θ/2)^2 := by
    convert cos_two_mul_eq_one_sub (θ/2) using 1; congr 1; ring
  have hden : 1+tan (θ/2)^2 ≠ 0 := by positivity
  have hsin : 2*tan (θ/2)/(1+tan (θ/2)^2) = sin θ := by
    rw [hs, tan_eq_sin_div_cos]
    field_simp
    nlinarith [sin_sq_add_cos_sq (θ/2),
      congrArg (fun z : ℝ => z*sin (θ/2)) (sin_sq_add_cos_sq (θ/2))]
  have hcos : 2*tan (θ/2)^2/(1+tan (θ/2)^2) = 1-cos θ := by
    rw [hh, tan_eq_sin_div_cos]
    field_simp
    nlinarith [sin_sq_add_cos_sq (θ/2),
      congrArg (fun z : ℝ => z*sin (θ/2)^2) (sin_sq_add_cos_sq (θ/2))]
  apply Subtype.ext
  change matrix ((tan (θ/2)) • k) = _
  rw [matrix_axis k hk, rotationExp_axis k hk θ hθ, hsin, hcos]

def rotationLog (q : Vec3) : Vec3 := (2*arctan (enorm q)) • Jacobian.unitAxis q

theorem rotationLog_norm (q : Vec3) : enorm (rotationLog q) = 2*arctan (enorm q) := by
  by_cases hq : q = 0
  · simp [hq, rotationLog, Jacobian.unitAxis, enorm]
  · have hn : 0 < enorm q := lt_of_le_of_ne (enorm_nonneg q)
      (Ne.symm (mt (enorm_eq_zero_iff q).mp hq))
    rw [rotationLog, enorm_smul, Gravity.unit_enorm _ (Jacobian.unitAxis_unit q hn), mul_one,
      abs_of_pos (mul_pos (by norm_num) (arctan_pos.mpr hn))]

theorem rotationLog_norm_lt_pi (q : Vec3) : enorm (rotationLog q) < π := by
  rw [rotationLog_norm]
  linarith [arctan_lt_pi_div_two (enorm q)]

theorem rotationLog_exp (q : Vec3) : rotationExp (rotationLog q) = rotation q := by
  by_cases hq : q = 0
  · subst q
    simp [rotationLog, Jacobian.unitAxis, enorm, rotationExp, skew_zero, rotation_zero]
  · have hn : 0 < enorm q := lt_of_le_of_ne (enorm_nonneg q)
      (Ne.symm (mt (enorm_eq_zero_iff q).mp hq))
    have hθ : 0 < 2*arctan (enorm q) := mul_pos (by norm_num) (arctan_pos.mpr hn)
    have hθπ : 2*arctan (enorm q) < π := by linarith [arctan_lt_pi_div_two (enorm q)]
    have h := rotation_axis_tan (Jacobian.unitAxis q) (Jacobian.unitAxis_unit q hn)
      (2*arctan (enorm q)) hθ hθπ
    rw [show 2*arctan (enorm q)/2 = arctan (enorm q) by ring, tan_arctan,
      Jacobian.unitAxis_reconstruct q hn] at h
    exact h.symm

theorem rotationExp_mem_domain (q : Vec3) (hq : enorm q < π) : rotationExp q ∈ domain := by
  by_cases hz : q = 0
  · subst q
    simpa [rotationExp, skew_zero] using one_mem_domain
  · have hn : 0 < enorm q := lt_of_le_of_ne (enorm_nonneg q)
      (Ne.symm (mt (enorm_eq_zero_iff q).mp hz))
    have h := rotation_axis_tan (Jacobian.unitAxis q) (Jacobian.unitAxis_unit q hn) (enorm q) hn hq
    rw [Jacobian.unitAxis_reconstruct q hn] at h
    rw [← h]
    exact rotation_mem_domain _

/-- The Cayley domain excludes precisely the rotation eigenvalue -1. -/
theorem domain_iff_no_minus_one (R : SO3) :
    R ∈ domain ↔ ∀ v : Vec3, rotate R v = -v → v = 0 := by
  change IsUnit (R.val+1).det ↔ _
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  constructor
  · intro hi v hv
    apply hi
    simp [Matrix.add_mulVec, rotate] at hv ⊢
    exact add_eq_zero_iff_eq_neg.mpr hv
  · intro h
    change Function.Injective (R.val+1).mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [Matrix.ker_mulVecLin_eq_bot_iff]
    intro v hv
    apply h v
    simpa only [Matrix.add_mulVec, Matrix.one_mulVec, rotate, add_eq_zero_iff_eq_neg] using hv

theorem det_add_one_trace (R : SO3) : (R.val+1).det = 2*(1+R.val.trace) := by
  have hd : R.val.det = 1 := R.property.2
  have ho : R.val*R.valᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp R.property.1
  have hadj : R.val.adjugate = R.valᵀ := by
    calc
      R.val.adjugate = R.val.adjugate*(R.val*R.valᵀ) := by rw [ho,Matrix.mul_one]
      _ = (R.val.adjugate*R.val)*R.valᵀ := by rw [Matrix.mul_assoc]
      _ = R.valᵀ := by rw [Matrix.adjugate_mul,hd,one_smul,Matrix.one_mul]
  have he (A : Mat3) : (A+1).det = A.det+A.trace+A.adjugate.trace+1 := by
    simp [Matrix.det_fin_three,Matrix.adjugate_fin_three,Matrix.trace,Fin.sum_univ_succ]
    ring
  rw [he,hd,hadj,Matrix.trace_transpose]
  ring

end GNC.Cayley

namespace GNC.PrincipalLog

/-- The principal image is exactly the Cayley chart domain of the rotation;
the two translation columns impose no extra restriction. -/
theorem domain_iff_rotation (X : SE23) : X ∈ domain ↔ X.rot ∈ Cayley.domain := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact Cayley.rotationExp_mem_domain (x 2) hx
  · intro hX
    let q := Cayley.rotationLog (Cayley.coordinates X.rot)
    have hq : enorm q < π := Cayley.rotationLog_norm_lt_pi _
    have he : rotationExp q = X.rot := (Cayley.rotationLog_exp _).trans (Cayley.rotation_coordinates X.rot hX)
    refine ⟨![Jacobian.inverseAt q X.pos,Jacobian.inverseAt q X.vel,q],hq,?_⟩
    apply SE23.ext
    · exact he
    · exact Jacobian.leftAt_inverseAt_all q X.vel (by linarith [pi_pos])
    · exact Jacobian.leftAt_inverseAt_all q X.pos (by linarith [pi_pos])

theorem domain_iff_no_minus_one (X : SE23) :
    X ∈ domain ↔ ∀ v : Vec3, rotate X.rot v = -v → v = 0 :=
  (domain_iff_rotation X).trans (Cayley.domain_iff_no_minus_one X.rot)

theorem domain_iff_det (X : SE23) : X ∈ domain ↔ (X.rot.val+1).det ≠ 0 := by
  rw [domain_iff_rotation]
  exact isUnit_iff_ne_zero

theorem domain_iff_trace (X : SE23) : X ∈ domain ↔ X.rot.val.trace ≠ -1 := by
  rw [domain_iff_det,Cayley.det_add_one_trace]
  constructor
  · intro h htr
    apply h
    rw [htr]
    norm_num
  · intro h hz
    apply h
    linarith

end GNC.PrincipalLog
