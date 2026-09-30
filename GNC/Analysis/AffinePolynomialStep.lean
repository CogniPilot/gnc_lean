import GNC.Analysis.PolynomialChain
import GNC.Analysis.LinearResponsePolynomial

/-! Polynomial certificates for a time-varying affine ODE with uncertain
coefficients. The coefficient errors may come from a certified numerical
reference. They are charged independently of the polynomial ODE residual.
The checker uses exact rational arithmetic and needs no exact STM.
-/
namespace GNC.AffinePolynomialStep
open PolynomialODE PolynomialBounds PolynomialOrder Planning.PolynomialKernel Set
variable {n : ℕ}

structure Step (n : ℕ) where
  coefficients : Fin n → List ℚ
  operator : Fin n → Fin n → List ℚ
  input : Fin n → List ℚ
  operatorError : ℚ
  inputError : ℚ
  duration : ℚ
  initialError : ℚ
  error : ℚ
  lipschitz : ℚ
  defect : ℚ

def residual (s : Step n) (i : Fin n) : List ℚ :=
  subtract (add (LinearResponsePolynomial.sumPolys
    (List.ofFn (fun j => multiply (s.operator i j) (s.coefficients j)))) (s.input i))
    (differentiate (s.coefficients i))

def rowGain (s : Step n) (i : Fin n) : ℚ :=
  ∑ j, (bound (s.operator i j) s.duration+s.operatorError)
def rowDefect (s : Step n) (i : Fin n) : ℚ :=
  bound (residual s i) s.duration+
    s.operatorError*(∑ j, bound (s.coefficients j) s.duration)+s.inputError

def Step.Valid (s : Step n) : Prop :=
  0≤s.duration ∧ 0≤s.initialError ∧ 0<s.error ∧
  0≤s.operatorError ∧ 0≤s.inputError ∧ 0≤s.lipschitz ∧ 0≤s.defect ∧
  s.initialError+s.duration*(s.lipschitz*s.error+s.defect)<s.error ∧
  ∀ i, rowGain s i≤s.lipschitz ∧ rowDefect s i≤s.defect

instance (s : Step n) : Decidable s.Valid := by unfold Step.Valid; infer_instance

theorem residual_value (s : Step n) (i : Fin n) (t : ℝ) :
    value (residual s i) t=
      (∑ j, value (s.operator i j) t*curve s.coefficients t j)+value (s.input i) t-
        value (differentiate (s.coefficients i)) t := by
  simp only [residual,value_subtract,value_add,LinearResponsePolynomial.value_sumPolys,
    List.map_ofFn,List.sum_ofFn,Function.comp_def,LinearResponsePolynomial.value_product]
  rfl

/-- The derivative-error budget includes perturbations of A and f, not
just the residual against their polynomial approximations. -/
theorem rate_error_bound (s : Step n) (hs : s.Valid) {t : ℝ}
    (ht : |t|≤(s.duration:ℝ)) (A : Fin n → Fin n → ℝ) (f x : Fin n → ℝ)
    (hA : ∀ i j, |A i j-value (s.operator i j) t|≤(s.operatorError:ℝ))
    (hf : ∀ i, |f i-value (s.input i) t|≤(s.inputError:ℝ))
    (hx : ‖x-curve s.coefficients t‖≤(s.error:ℝ)) :
    ‖(fun i => (∑ j, A i j*x j)+f i)-
      (fun i => value (differentiate (s.coefficients i)) t)‖≤
        (s.lipschitz:ℝ)*s.error+s.defect := by
  obtain ⟨hT,hE,hB,hAE,hFE,hL,hD,hclose,hrows⟩ := hs
  have hBr : (0:ℝ)≤s.error := by exact_mod_cast hB.le
  have hAr : (0:ℝ)≤s.operatorError := by exact_mod_cast hAE
  have hLr : (0:ℝ)≤s.lipschitz := by exact_mod_cast hL
  have hDr : (0:ℝ)≤s.defect := by exact_mod_cast hD
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hp (j) : |curve s.coefficients t j|≤(bound (s.coefficients j) s.duration:ℝ) :=
    bound_sound _ ht
  have ha (j) : |A i j|≤(bound (s.operator i j) s.duration:ℝ)+s.operatorError := by
    have hb := bound_sound (s.operator i j) ht
    change |value (s.operator i j) t|≤_ at hb
    have he := abs_add_le (A i j-value (s.operator i j) t) (value (s.operator i j) t)
    rw [sub_add_cancel] at he
    linarith [hA i j]
  have hxj (j) : |x j-curve s.coefficients t j|≤(s.error:ℝ) := by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm (x-curve s.coefficients t) j).trans hx
  have hfirst : |∑ j, A i j*(x j-curve s.coefficients t j)|≤(rowGain s i:ℝ)*s.error := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simp only [rowGain,Rat.cast_sum,Rat.cast_add,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    exact mul_le_mul (ha j) (hxj j) (abs_nonneg _) ((abs_nonneg _).trans (ha j))
  have hsecond : |∑ j, (A i j-value (s.operator i j) t)*curve s.coefficients t j|≤
      (s.operatorError:ℝ)*(∑ j, (bound (s.coefficients j) s.duration:ℝ)) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    exact mul_le_mul (hA i j) (hp j) (abs_nonneg _) hAr
  have hres := bound_sound (residual s i) ht
  change |value (residual s i) t|≤_ at hres
  have he : (∑ j, A i j*x j)+f i-value (differentiate (s.coefficients i)) t=
      (∑ j, A i j*(x j-curve s.coefficients t j))+
      (∑ j, (A i j-value (s.operator i j) t)*curve s.coefficients t j)+
      value (residual s i) t+(f i-value (s.input i) t) := by
    rw [residual_value]
    simp only [mul_sub,sub_mul,Finset.sum_sub_distrib]
    ring
  simp only [Pi.sub_apply,Real.norm_eq_abs]
  rw [he]
  have hsum := ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)).trans
      (add_le_add (add_le_add (add_le_add hfirst hsecond) hres) (hf i))
  have hr1 : (rowGain s i:ℝ)≤s.lipschitz := by exact_mod_cast (hrows i).1
  have hr2 : (rowDefect s i:ℝ)≤s.defect := by exact_mod_cast (hrows i).2
  simp only [rowDefect,Rat.cast_add,Rat.cast_mul,Rat.cast_sum] at hr2
  nlinarith [mul_le_mul_of_nonneg_right hr1 hBr]

/-- A checked polynomial encloses the exact affine trajectory throughout
the step. The true coefficient functions need not be polynomials. -/
theorem step_sound (s : Step n) (hs : s.Valid)
    (A : ℝ → Fin n → Fin n → ℝ) (f x : ℝ → Fin n → ℝ) (hx : Continuous x)
    (hd : ∀ t ∈ Icc (0:ℝ) s.duration,
      HasDerivAt x (fun i => (∑ j, A t i j*x t j)+f t i) t)
    (hA : ∀ t ∈ Icc (0:ℝ) s.duration, ∀ i j,
      |A t i j-value (s.operator i j) t|≤(s.operatorError:ℝ))
    (hf : ∀ t ∈ Icc (0:ℝ) s.duration, ∀ i,
      |f t i-value (s.input i) t|≤(s.inputError:ℝ))
    (hi : ‖x 0-curve s.coefficients 0‖≤(s.initialError:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) s.duration,
      ‖x t-curve s.coefficients t‖<(s.error:ℝ) := by
  have hs' := hs
  obtain ⟨hT,hE,hB,hAE,hFE,hL,hD,hclose,hrows⟩ := hs
  have hTr : (0:ℝ)≤s.duration := by exact_mod_cast hT
  have hLr : (0:ℝ)≤s.lipschitz := by exact_mod_cast hL
  have hBr : (0:ℝ)<s.error := by exact_mod_cast hB
  have hDr : (0:ℝ)≤s.defect := by exact_mod_cast hD
  have hCr : (0:ℝ)≤(s.lipschitz:ℝ)*s.error+s.defect := by positivity
  have hclosed : (s.initialError:ℝ)+(s.duration:ℝ)*
      ((s.lipschitz:ℝ)*s.error+s.defect)<s.error := by exact_mod_cast hclose
  have hc : Continuous (curve s.coefficients) := continuous_iff_continuousAt.mpr
    fun t => (curve_derivative s.coefficients t).continuousAt
  apply IntegralTube.prefix_closure ((hx.sub hc).norm) (hi.trans_lt (by nlinarith))
  intro t ht hpref
  have hsub (u : ℝ) (hu : u ∈ Icc 0 t) : u ∈ Icc (0:ℝ) s.duration :=
    ⟨hu.1,hu.2.trans ht.2⟩
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu => ((hd u (hsub u hu)).sub (curve_derivative s.coefficients u)).hasDerivWithinAt)
    (fun u hu => rate_error_bound s hs'
      (by rw [abs_of_nonneg hu.1]; exact (hsub u (Ico_subset_Icc_self hu)).2)
      (A u) (f u) (x u) (hA u (hsub u (Ico_subset_Icc_self hu)))
      (hf u (hsub u (Ico_subset_Icc_self hu))) (hpref u (Ico_subset_Icc_self hu)))
    t (right_mem_Icc.mpr ht.1)
  simp only [sub_zero,Pi.sub_apply] at hm
  have hn := norm_sub_norm_le (x t-curve s.coefficients t) (x 0-curve s.coefficients 0)
  nlinarith [mul_le_mul_of_nonneg_left ht.2 hCr]

end GNC.AffinePolynomialStep
