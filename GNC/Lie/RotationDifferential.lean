import GNC.Lie.JacobianDifferential

noncomputable section
open Matrix Real NormedSpace
open scoped Matrix Matrix.Norms.Operator Topology
namespace GNC

theorem skew_add (u v : Vec3) : skew (u+v) = skew u + skew v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [skew, add_comm]

theorem skew_cross (u v : Vec3) : skew (u ⨯₃ v) = skew u*skew v-skew v*skew u := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [skew, cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem skew_sandwich (k u : Vec3) : skew k*skew u*skew k = -(k ⬝ᵥ u) • skew k := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [skew, dotProduct, Fin.sum_univ_succ] <;> ring

theorem skew_derivative {f : ℝ → Vec3} {u : Vec3} {t : ℝ} (hf : HasDerivAt f u t) :
    HasDerivAt (fun s => skew (f s)) (skew u) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> first
    | exact hasDerivAt_const t 0
    | exact hasDerivAt_pi.mp hf _
    | exact (hasDerivAt_pi.mp hf _).neg

def rotationDerivative (q u : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (((enorm q)*cos (enorm q)-sin (enorm q))*(q ⬝ᵥ u)/enorm q^3) • skew q +
  (sin (enorm q)/enorm q) • skew u +
  (((enorm q)*sin (enorm q)-2+2*cos (enorm q))*(q ⬝ᵥ u)/enorm q^4) • skew q^2 +
  ((1-cos (enorm q))/enorm q^2) • (skew u*skew q+skew q*skew u)

theorem rotationExp_derivative (q u : Vec3) (hq : 0 < enorm q) :
    HasDerivAt (fun s : ℝ => (rotationExp (q+s • u)).val) (rotationDerivative q u) 0 := by
  have hq0 : q ≠ 0 := mt (enorm_eq_zero_iff q).mpr hq.ne'
  have hp : HasDerivAt (fun s : ℝ => q+s • u) u 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add q
  have hn : HasDerivAt (fun s : ℝ => enorm (q+s • u)) (q ⬝ᵥ u/enorm q) 0 := by
    simpa using Jacobian.affine_enorm_derivative q u 0 (by simpa using hq0)
  have hc := hn.sin.div hn (by simpa using hq.ne')
  have ha := (hn.cos.const_sub 1).div (hn.pow 2) (by simpa using pow_ne_zero 2 hq.ne')
  have hS := skew_derivative hp
  have hd := ((hc.smul hS).const_add 1).add (ha.smul (hS.mul hS))
  simp_rw [rotationExp_formula]
  convert hd using 1
  · funext s; dsimp; simp only [pow_two]
  · dsimp [rotationDerivative]
    simp only [zero_smul, add_zero, pow_two]
    match_scalars <;> field_simp <;> ring

theorem rotationDerivative_axis (k u : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) :
    rotationDerivative (t • k) u =
      (((t*cos t-sin t)/t)*(k ⬝ᵥ u)) • skew k + (sin t/t) • skew u +
      (((t*sin t-2+2*cos t)/t)*(k ⬝ᵥ u)) • skew k^2 +
      ((1-cos t)/t) • (skew u*skew k+skew k*skew u) := by
  have hn : enorm (t • k) = t := by
    rw [enorm_smul, Gravity.unit_enorm k hk, abs_of_pos ht, mul_one]
  simp only [rotationDerivative, hn, skew_smul, smul_dotProduct, smul_eq_mul,
    smul_smul, smul_pow, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  match_scalars <;> field_simp <;> ring

theorem rotationExp_axis (k : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) :
    (rotationExp (t • k)).val = 1+sin t • skew k+(1-cos t) • skew k^2 := by
  have hn : enorm (t • k) = t := by
    rw [enorm_smul, Gravity.unit_enorm k hk, abs_of_pos ht, mul_one]
  rw [rotationExp_formula, hn, skew_smul]
  simp only [smul_smul, smul_pow]
  match_scalars <;> field_simp

theorem skew_left_axis (k u : Vec3) (t : ℝ) :
    skew (Jacobian.left k t u) = (sin t/t) • skew u +
      ((1-sin t/t)*(k ⬝ᵥ u)) • skew k +
      ((1-cos t)/t) • (skew k*skew u-skew u*skew k) := by
  simp only [Jacobian.left, Jacobian.planeMap, Axis.transverse, Axis.axial,
    sub_eq_add_neg, skew_add, skew_smul, skew_cross]
  have hn : skew (-((k ⬝ᵥ u) • k)) = -(k ⬝ᵥ u) • skew k := by
    rw [← neg_smul, skew_smul]
  rw [hn]
  module

/-- Left-trivialized derivative of the actual SO(3) exponential. -/
theorem rotationDerivative_trivialized (k u : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) :
    rotationDerivative (t • k) u = skew (Jacobian.left k t u) * (rotationExp (t • k)).val := by
  rw [rotationDerivative_axis k u hk t ht, rotationExp_axis k hk t ht, skew_left_axis]
  have hc : skew k^3 = -skew k := by
    simpa [Gravity.unit_enorm k hk] using skew_cube k
  have hKu := skew_sandwich k u
  have hKuu : skew k*skew u*skew k^2 = -(k ⬝ᵥ u) • skew k^2 := by
    rw [pow_two, ← Matrix.mul_assoc, hKu, Matrix.smul_mul]
  have hUK : skew u*skew k*skew k^2 = -(skew u*skew k) := by
    rw [Matrix.mul_assoc, ← pow_succ', hc, Matrix.mul_neg]
  have hUK2 : skew u*skew k*skew k = skew u*skew k^2 := by
    rw [Matrix.mul_assoc, pow_two]
  have hK2 : skew k*skew k = skew k^2 := by noncomm_ring
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_add, smul_sub, smul_smul,
    ← Matrix.mul_assoc, hK2, ← pow_succ', hc, hKu, hKuu, hUK, hUK2,
    smul_neg]
  have hs := sin_sq_add_cos_sq t
  have hs' := congrArg (fun z : ℝ => z*(k ⬝ᵥ u)) hs
  match_scalars <;> field_simp <;> nlinarith

end GNC
