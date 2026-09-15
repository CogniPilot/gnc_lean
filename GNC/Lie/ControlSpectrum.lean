import GNC.Lie.ControlOperator
import GNC.Lie.JacobianSpectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! The exact induced norm in equation (60), obtained from mathlib's
Rayleigh-quotient characterization and an explicit maximizing eigenvector. -/
noncomputable section
open Matrix Real
open scoped Matrix RealInnerProductSpace
namespace GNC.Control

theorem mLinear_symmetric (k u : Vec3) (a b : ℝ) :
    (mLinear k a b u).IsSymmetric := by
  intro v w
  simp only [Jacobian.inner_ofLp]
  change mAction k a b u (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp w =
    WithLp.ofLp v ⬝ᵥ mAction k a b u (WithLp.ofLp w)
  simp only [mAction, Axis.transverse, Axis.axial, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm (WithLp.ofLp v) k,
    dotProduct_comm (WithLp.ofLp v) u]
  ring

theorem mAction_quadratic (k u v : Vec3) (a b : ℝ) :
    mAction k a b u v ⬝ᵥ v =
      -(a*(k ⬝ᵥ u))*(lengthSq v-(k ⬝ᵥ v)^2) +
        2*b*(k ⬝ᵥ v)*(Axis.transverse k u ⬝ᵥ v) := by
  simp only [mAction, Axis.transverse, Axis.axial, add_dotProduct,
    sub_dotProduct, smul_dotProduct, smul_eq_mul, dot_self_lengthSq]
  ring

private theorem quadratic_bound (A b L S h z c : ℝ) (hc : 0 < c)
    (hroot : c^2 = |A| * c+b^2*L) (hS : 0 ≤ S) (hz : z^2 ≤ L*S) :
    |-A*S+2*b*h*z| ≤ c*(S+h^2) := by
  have hz' := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hz)
  have hr := congrArg (fun x : ℝ => x*S) hroot
  have hA := mul_le_mul_of_nonneg_right (le_abs_self A) hS
  have hA' := mul_le_mul_of_nonneg_right (neg_le_abs A) hS
  have hlo : -c*(S+h^2) ≤ -|A| * S+2*b*h*z := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith only [sq_nonneg (c*h+b*z),hz',hr]
  have hhi : |A| * S+2*b*h*z ≤ c*(S+h^2) := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith only [sq_nonneg (c*h-b*z),hz',hr]
  exact abs_le.mpr ⟨by nlinarith only [hlo,hA], by nlinarith only [hhi,hA']⟩

theorem mLinear_norm_le_root (k u : Vec3) (hk : k ⬝ᵥ k = 1)
    (a b c : ℝ) (hc : 0 < c)
    (hroot : c^2 = |a*(k ⬝ᵥ u)| * c+b^2*lengthSq (Axis.transverse k u)) :
    ‖(mLinear k a b u).toContinuousLinearMap‖ ≤ c := by
  let T := (mLinear k a b u).toContinuousLinearMap
  rw [T.norm_eq_iSup_rayleighQuotient (mLinear_symmetric k u a b)]
  apply ciSup_le
  intro v
  by_cases hv : v = 0
  · simp [hv, hc.le]
  have hvp : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [Jacobian.inner_ofLp]
  change |(mAction k a b u (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v) / ‖v‖^2| ≤ c
  rw [abs_div, abs_of_pos hvp, div_le_iff₀ hvp, mAction_quadratic]
  have hs := Axis.dot_sq_le k (WithLp.ofLp v) hk
  have hz := transverse_cauchy k u (WithLp.ofLp v) hk
  rw [← Axis.transverse_sq k u hk] at hz
  have h := quadratic_bound (a*(k ⬝ᵥ u)) b (lengthSq (Axis.transverse k u))
    (lengthSq (WithLp.ofLp v)-(k ⬝ᵥ WithLp.ofLp v)^2)
    (k ⬝ᵥ WithLp.ofLp v) (Axis.transverse k u ⬝ᵥ WithLp.ofLp v) c hc hroot
    (sub_nonneg.mpr hs) hz
  have hn : ‖v‖^2 = lengthSq (WithLp.ofLp v) := enorm_sq _
  simpa only [sub_add_cancel, hn] using h

theorem mAction_eigenvector (k u : Vec3) (hk : k ⬝ᵥ k = 1) (a b μ : ℝ)
    (hμ : μ^2+a*(k ⬝ᵥ u)*μ = b^2*lengthSq (Axis.transverse k u)) :
    mAction k a b u ((μ+a*(k ⬝ᵥ u)) • k+b • Axis.transverse k u) =
      μ • ((μ+a*(k ⬝ᵥ u)) • k+b • Axis.transverse k u) := by
  have hkw : k ⬝ᵥ Axis.transverse k u = 0 := by
    simp [Axis.transverse, Axis.axial, hk]
  have hwk : Axis.transverse k u ⬝ᵥ k = 0 := by rw [dotProduct_comm, hkw]
  have htrans : Axis.transverse k ((μ+a*(k ⬝ᵥ u)) • k+b • Axis.transverse k u) =
      b • Axis.transverse k u := by
    simp [Axis.transverse, Axis.axial, dotProduct_add, hk]
  simp only [mAction, htrans, dotProduct_add, dotProduct_smul, smul_eq_mul,
    hk, hkw, hwk, dot_self_lengthSq, mul_one, mul_zero, add_zero, zero_add]
  have hr : b^2*lengthSq (Axis.transverse k u) = μ*(μ+a*(k ⬝ᵥ u)) := by nlinarith only [hμ]
  calc
    _ = (b^2*lengthSq (Axis.transverse k u)) • k+(b*μ) • Axis.transverse k u := by module
    _ = _ := by rw [hr]; module

def normFormula (k u : Vec3) (a b : ℝ) : ℝ :=
  (|a*(k ⬝ᵥ u)|+√((a*(k ⬝ᵥ u))^2+4*b^2*lengthSq (Axis.transverse k u)))/2

theorem normFormula_root (k u : Vec3) (a b : ℝ) :
    (normFormula k u a b)^2 = |a*(k ⬝ᵥ u)| * normFormula k u a b+
      b^2*lengthSq (Axis.transverse k u) := by
  have hs := Real.sq_sqrt (show 0 ≤ (a*(k ⬝ᵥ u))^2+4*b^2*lengthSq (Axis.transverse k u) by
    positivity [lengthSq_nonneg (Axis.transverse k u)])
  unfold normFormula
  nlinarith [sq_abs (a*(k ⬝ᵥ u))]

theorem mLinear_norm_formula_of_transverse_ne (k u : Vec3) (hk : k ⬝ᵥ k = 1)
    (a b : ℝ) (hb : 0 < b) (hw : Axis.transverse k u ≠ 0) :
    ‖(mLinear k a b u).toContinuousLinearMap‖ = normFormula k u a b := by
  let A := a*(k ⬝ᵥ u)
  let L := lengthSq (Axis.transverse k u)
  let c := normFormula k u a b
  have hL : 0 < L := lt_of_le_of_ne (lengthSq_nonneg _)
    (Ne.symm (mt (lengthSq_eq_zero_iff _).mp hw))
  have hroot : c^2 = |A| * c+b^2*L := normFormula_root k u a b
  have hc : 0 < c := by
    have hs : 0 < A^2+4*b^2*L := by positivity
    exact div_pos (add_pos_of_nonneg_of_pos (abs_nonneg A) (Real.sqrt_pos.mpr hs)) (by norm_num)
  apply le_antisymm (mLinear_norm_le_root k u hk a b c hc hroot)
  let μ := if 0 ≤ A then -c else c
  have hμabs : |μ| = c := by
    dsimp only [μ]
    split_ifs <;> simp [abs_of_pos hc]
  have hμ : μ^2+A*μ = b^2*L := by
    dsimp only [μ]
    split_ifs with hA
    · rw [abs_of_nonneg hA] at hroot
      nlinarith only [hroot]
    · rw [abs_of_neg (lt_of_not_ge hA)] at hroot
      nlinarith only [hroot]
  let v := (μ+A) • k+b • Axis.transverse k u
  have hv : v ≠ 0 := by
    intro hv
    have h := congrArg (fun x : Vec3 => Axis.transverse k u ⬝ᵥ x) hv
    have hwk : Axis.transverse k u ⬝ᵥ k = 0 := by
      simp [Axis.transverse, Axis.axial, hk, dotProduct_comm u k]
    have hzero : b*L = 0 := by
      simpa [v, dotProduct_add, dotProduct_smul, hwk, dot_self_lengthSq, L] using h
    exact (mul_pos hb hL).ne' hzero
  have he := mAction_eigenvector k u hk a b μ hμ
  have h := (mLinear k a b u).toContinuousLinearMap.le_opNorm (WithLp.toLp 2 v)
  change enorm (mAction k a b u v) ≤ _ at h
  rw [he, enorm_smul, hμabs] at h
  have hvp : 0 < enorm v := lt_of_le_of_ne (enorm_nonneg v)
    (Ne.symm (mt (enorm_eq_zero_iff v).mp hv))
  exact (mul_le_mul_iff_left₀ hvp).mp (by simpa [mul_comm] using h)

/-- Equation (60), for the actual Euclidean operator attached to M. -/
theorem mCLM_norm_formula (k u : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    ‖mCLM k t u‖ =
      (|(k ⬝ᵥ u)| * Coefficients.alpha t+
        √((k ⬝ᵥ u)^2*(Coefficients.alpha t)^2+
          4*lengthSq (Axis.transverse k u)*(Coefficients.beta t/t)^2))/2 := by
  have hb := div_pos (Coefficients.beta_pos t ht htπ) ht
  have ha : 0 < Coefficients.alpha t := lt_trans (show 0 < 2*Coefficients.beta t/t from div_pos (mul_pos (by norm_num) (Coefficients.beta_pos t ht htπ)) ht)
    (Coefficients.alpha_gt_two_beta_div t ht htπ)
  by_cases hw : Axis.transverse k u = 0
  · have hu : u = (k ⬝ᵥ u) • k := sub_eq_zero.mp hw
    rw [hu, mCLM_axial_norm k hk t _ ht htπ]
    simp only [dotProduct_smul, smul_eq_mul, hk, mul_one]
    have htrans : Axis.transverse k ((k ⬝ᵥ u) • k) = 0 := by
      simp [Axis.transverse, Axis.axial, hk]
    rw [htrans]
    simp only [lengthSq, Pi.zero_apply,
      enorm_smul, Gravity.unit_enorm k hk, mul_one]
    norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, mul_zero, zero_mul]
    rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos ha]
    ring
  · change ‖(mLinear k (Coefficients.alpha t) (Coefficients.beta t/t) u).toContinuousLinearMap‖ = _
    rw [mLinear_norm_formula_of_transverse_ne k u hk _ _ hb hw, normFormula,
      abs_mul, abs_of_pos ha]
    simp only [mul_pow, mul_comm, mul_left_comm, mul_assoc]

/-- The action of (59) in the orthonormal triad {k,w,k×w}. -/
theorem mAction_triad (k w : Vec3) (hk : k ⬝ᵥ k = 1) (hw : w ⬝ᵥ w = 1)
    (hkw : k ⬝ᵥ w = 0) (a b r s x y z : ℝ) :
    mAction k a b (r • k+s • w) (x • k+y • w+z • (k ⨯₃ w)) =
      (s*b*y) • k+(s*b*x-r*a*y) • w+(-r*a*z) • (k ⨯₃ w) := by
  have hwk : w ⬝ᵥ k = 0 := by rw [dotProduct_comm, hkw]
  simp [mAction, Axis.transverse, Axis.axial, dotProduct_add, dotProduct_smul,
    add_dotProduct, smul_dotProduct, dot_self_cross, dot_cross_self, hk, hw, hkw, hwk]
  module

/-- The remaining direction is an eigenvector with eigenvalue -a u∥. -/
theorem mAction_cross_eigenvector (k u : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) :
    mAction k a b u (k ⨯₃ u) = (-(a*(k ⬝ᵥ u))) • (k ⨯₃ u) := by
  simp [mAction, Axis.transverse, Axis.axial, sub_dotProduct, smul_dotProduct,
    dot_self_cross, dot_cross_self]

end GNC.Control
