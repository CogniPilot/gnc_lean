import GNC.Dynamics.LieErrorReconstruction

/-! Polynomial checks for a three-axis SO(3) left Jacobian. The delivered
map remains exact. The polynomial below is used only in residual checks,
with its operator error charged explicitly, including at zero rotation. -/
noncomputable section
namespace GNC.JacobianPolynomial
open Matrix Real Set

def firstCoefficient (s : ℝ) : ℝ := 1/2-s/24+s^2/720-s^3/40320
def secondCoefficient (s : ℝ) : ℝ := 1/6-s/120+s^2/5040-s^3/362880
def apply (φ v : Vec3) : Vec3 :=
  v+firstCoefficient (lengthSq φ) • (φ ⨯₃ v)+
    secondCoefficient (lengthSq φ) • (φ ⨯₃ (φ ⨯₃ v))
def tail (s : ℝ) : ℝ := s^9/3628800+s^10/39916800
def sine (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040+x^9/362880

theorem tail_nonneg {s : ℝ} (hs : 0≤s) : 0≤tail s := by
  unfold tail
  positivity

theorem tail_mono {s t : ℝ} (hs : 0≤s) (hst : s≤t) : tail s≤tail t := by
  unfold tail
  gcongr

private theorem sine_taylor (x : ℝ) : taylorWithinEval sin 10 univ 0 x=sine x := by
  norm_num [sine,taylorWithinEval_succ,iteratedDerivWithin_univ,iteratedDeriv_succ,
    Real.deriv_sin,deriv_cos',deriv.neg',deriv_neg]
  ring

theorem sine_bound {x : ℝ} (hx : 0≤x) : |sin x-sine x|≤x^11/39916800 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x; norm_num [sine]
  · have h := TrigonometricPolynomial.taylor_bound_pos sin contDiff_sin 10
      (abs_iteratedDeriv_sin_le_one 11) hp
    simpa only [sine_taylor] using h

theorem error_bound (φ v : Vec3) : enorm (Jacobian.leftAt φ v-apply φ v)≤tail (enorm φ)*enorm v := by
  by_cases hz : enorm φ=0
  · rw [(enorm_eq_zero_iff φ).mp hz]
    have h0 : enorm (0:Vec3)=0 := (enorm_eq_zero_iff _).mpr rfl
    simp [Jacobian.leftAt,apply,h0,tail]
  · have hp : 0<enorm φ := lt_of_le_of_ne (enorm_nonneg φ) (Ne.symm hz)
    have hsq : lengthSq φ=(enorm φ)^2 := (enorm_sq φ).symm
    have h1 : (1-cos (enorm φ))/(enorm φ)^2-firstCoefficient (lengthSq φ)=
        (1-cos (enorm φ)-OcticPointing.cosineLoss (enorm φ))/(enorm φ)^2 := by
      rw [hsq]
      dsimp [firstCoefficient,OcticPointing.cosineLoss]
      field_simp <;> ring
    have h2 : (enorm φ-sin (enorm φ))/(enorm φ)^3-secondCoefficient (lengthSq φ)=
        (sine (enorm φ)-sin (enorm φ))/(enorm φ)^3 := by
      rw [hsq]
      dsimp [secondCoefficient,sine]
      field_simp <;> ring
    have he : Jacobian.leftAt φ v-apply φ v=
        ((1-cos (enorm φ)-OcticPointing.cosineLoss (enorm φ))/(enorm φ)^2) • (φ ⨯₃ v)+
        ((sine (enorm φ)-sin (enorm φ))/(enorm φ)^3) • (φ ⨯₃ (φ ⨯₃ v)) := by
      rw [←h1,←h2]
      simp only [Jacobian.leftAt,apply]
      module
    have hc := OcticPointing.cosine_bound (enorm φ)
    rw [abs_of_nonneg hp.le] at hc
    have hs := sine_bound hp.le
    rw [abs_sub_comm] at hs
    have ha : |(1-cos (enorm φ)-OcticPointing.cosineLoss (enorm φ))/(enorm φ)^2|≤
        (enorm φ)^8/3628800 := by
      simp only [abs_div,abs_pow,abs_of_nonneg hp.le]
      apply (div_le_div_of_nonneg_right hc (sq_nonneg _)).trans_eq
      field_simp
    have hb : |(sine (enorm φ)-sin (enorm φ))/(enorm φ)^3|≤
        (enorm φ)^8/39916800 := by
      simp only [abs_div,abs_pow,abs_of_nonneg hp.le]
      apply (div_le_div_of_nonneg_right hs (pow_nonneg hp.le 3)).trans_eq
      field_simp
    have hn1 := cross_enorm_le φ v
    have hn2 := (cross_enorm_le φ (φ ⨯₃ v)).trans
      (mul_le_mul_of_nonneg_left hn1 hp.le)
    rw [he]
    apply (enorm_add_le _ _).trans
    rw [enorm_smul,enorm_smul]
    convert add_le_add
      (mul_le_mul ha hn1 (enorm_nonneg _) (by positivity))
      (mul_le_mul hb hn2 (enorm_nonneg _) (by positivity)) using 1 <;> dsimp [tail] <;> ring

/-- Exact Gram reduction for any quadratic skew polynomial. The scalar
coefficient can itself be a polynomial in the squared attitude magnitude. -/
theorem gram (φ v : Vec3) (a b : ℝ) :
    enorm (v+a • (φ ⨯₃ v)+b • (φ ⨯₃ (φ ⨯₃ v)))^2=
      enorm v^2+(a^2-2*b+lengthSq φ*b^2)*enorm (φ ⨯₃ v)^2 := by
  simp [enorm_sq,lengthSq,crossProduct,Pi.add_apply,Pi.smul_apply,smul_eq_mul,vecHead,vecTail]
  ring

theorem apply_gram (φ v : Vec3) :
    enorm (apply φ v)^2=enorm v^2+
      (firstCoefficient (lengthSq φ)^2-2*secondCoefficient (lengthSq φ)+
        lengthSq φ*secondCoefficient (lengthSq φ)^2)*enorm (φ ⨯₃ v)^2 :=
  gram φ v _ _

end GNC.JacobianPolynomial
