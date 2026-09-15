import GNC.Analysis.QuarticPointing
import GNC.Analysis.FundamentalSolution
import GNC.Analysis.MonomialSecondOrderBound

/-! A genuine degree-four uncertainty response: propagate five coefficient
ODEs for the translated sine/cosine jet. The unknown rate does not enter
those ODEs. The complete source truncation has an explicit t^5 envelope.
This is a refinable classical comparator, not a global quartic lower bound. -/
noncomputable section
namespace GNC.QuarticHarmonicResponse
open Real Set Polynomial
open scoped BigOperators

def forcing (c d t : ℝ) : ℝ :=
  144*(cos (c*t)*(1-QuarticPointing.cosineLoss (d*t))-
    sin (c*t)*QuarticPointing.sine (d*t))

theorem source_bound (c d t : ℝ) :
    |144*cos ((c+d)*t)-forcing c d t|≤
      144*(|d*t|^5/120+|d*t|^6/720) := by
  have h := QuarticPointing.source_bound (d*t) (sin (c*t)) (cos (c*t))
  have he : 144*cos ((c+d)*t)-forcing c d t =
      -144*((sin (d*t)*sin (c*t)+(1-cos (d*t))*cos (c*t))-
        (QuarticPointing.sine (d*t)*sin (c*t)+
          QuarticPointing.cosineLoss (d*t)*cos (c*t))) := by
    rw [add_mul,cos_add]; dsimp [forcing]; ring
  rw [he,abs_mul,abs_neg]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<144)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤144)
  simp only [Real.norm_eq_abs,smul_eq_mul] at h
  apply h.trans
  have hs := Real.abs_sin_le_one (c*t)
  have hc := Real.abs_cos_le_one (c*t)
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤|d*t|^5/120),
    mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ)≤|d*t|^6/720)]

def sourceBudget (h : ℝ) : ℝ := 144*(h^5/120+h^6/720)

theorem source_profile {d h t : ℝ} (c : ℝ) (hd : |d|≤h) (ht : t ∈ Icc (0:ℝ) 1) :
    |144*cos ((c+d)*t)-forcing c d t|≤sourceBudget h*t^5 := by
  have hh : 0≤h := (abs_nonneg d).trans hd
  have h5 : |d|^5≤h^5 := by gcongr
  have h6 : |d|^6≤h^6 := by gcongr
  have ht6 : t^6≤t^5 := by
    calc
      _ = t^5*t := by ring
      _ ≤ t^5*1 := mul_le_mul_of_nonneg_left ht.2 (pow_nonneg ht.1 _)
      _ = _ := mul_one _
  apply (source_bound c d t).trans
  rw [abs_mul,abs_of_nonneg ht.1,mul_pow,mul_pow]
  dsimp [sourceBudget]
  have ha := mul_le_mul_of_nonneg_right h5 (pow_nonneg ht.1 5)
  have hb := (mul_le_mul_of_nonneg_right h6 (pow_nonneg ht.1 6)).trans
    (mul_le_mul_of_nonneg_left ht6 (pow_nonneg hh 6))
  nlinarith

def coefficient (c t : ℝ) : Fin 5 → ℝ :=
  ![144*cos (c*t),-144*t*sin (c*t),-72*t^2*cos (c*t),
    24*t^3*sin (c*t),6*t^4*cos (c*t)]

theorem coefficient_sum (c d t : ℝ) :
    (∑ i : Fin 5, d^(i:ℕ)*coefficient c t i)=forcing c d t := by
  simp [Fin.sum_univ_succ,coefficient,forcing,QuarticPointing.sine,
    QuarticPointing.cosineLoss]
  ring

def operator (k : ℝ) : (ℝ×ℝ) →ₗ[ℝ] (ℝ×ℝ) where
  toFun x := (x.2,-k*x.1)
  map_add' _ _ := by ext <;> simp [mul_add]
  map_smul' _ _ := by ext <;> simp [mul_assoc,mul_left_comm]

theorem exists_coefficient_response (k c : ℝ) (i : Fin 5) :
    ∃ x : ℝ → ℝ×ℝ, x 0=0 ∧ ∀ t,
      HasDerivAt x (operator k (x t)+(0,coefficient c t i)) t := by
  have hc : Continuous (fun t => ((0:ℝ),coefficient c t i)) := by
    fin_cases i <;> dsimp [coefficient] <;> fun_prop
  obtain ⟨x,hx,_⟩ := ForcedResponse.exists_unique_response
    (fun _ => (operator k).toContinuousLinearMap) continuous_const _ hc 0
  exact ⟨x,hx⟩

def basis (k c : ℝ) (i : Fin 5) : ℝ → ℝ×ℝ :=
  (exists_coefficient_response k c i).choose
def response (k c d t : ℝ) : ℝ×ℝ := ∑ i : Fin 5, d^(i:ℕ) • basis k c i t

theorem initial (k c d : ℝ) : response k c d 0=0 := by
  simp [response,basis,(exists_coefficient_response k c _).choose_spec.1]

theorem derivative (k c d t : ℝ) : HasDerivAt (response k c d)
    ((response k c d t).2,-k*(response k c d t).1+forcing c d t) t := by
  have hd (i : Fin 5) := ((exists_coefficient_response k c i).choose_spec.2 t).const_smul (d^(i:ℕ))
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => hd i)
  convert h using 1
  ext <;> simp [response,basis,operator,Fin.sum_univ_succ,coefficient,forcing,
    QuarticPointing.sine,QuarticPointing.cosineLoss] <;> ring

def velocityPolynomial (k c t : ℝ) : Polynomial ℝ :=
  ∑ i : Fin 5, monomial (i:ℕ) ((basis k c i t).2)

theorem velocityPolynomial_eval (k c d t : ℝ) :
    (velocityPolynomial k c t).eval d=(response k c d t).2 := by
  simp [velocityPolynomial,response,eval_finset_sum,eval_monomial,mul_comm,Prod.snd_sum]

theorem velocityPolynomial_degree (k c t : ℝ) : (velocityPolynomial k c t).natDegree≤4 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans (by omega)

end GNC.QuarticHarmonicResponse
