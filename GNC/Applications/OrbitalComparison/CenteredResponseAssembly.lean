import GNC.Applications.OrbitalComparison.CenteredResponseData
import GNC.Applications.OrbitalComparison.CenteredResponseReference

/-! Assemble the checked coefficient residuals before transferring to the
physical gravity operators. Quadratic features enumerate unordered pairs,
with a half factor only on the diagonal. -/
noncomputable section
set_option maxHeartbeats 0
namespace GNC.OrbitalComparison.CenteredResponseData
open CartesianResponsePolynomial Matrix Set
open scoped RealInnerProductSpace

def firstResponse (w : Fin 8 → ℝ) (t : ℝ) : E3 := WithLp.toLp 2 (combination first w t)
def productWeights (w : Fin 8 → ℝ) (j : Fin 36) : ℝ := w (pairLeft j)*w (pairRight j)
def secondResponse (w : Fin 8 → ℝ) (t : ℝ) : E3 :=
  WithLp.toLp 2 (combination second (productWeights w) t)

theorem product_weights_bound (w : Fin 8 → ℝ) (hw : ∀ j, |w j|≤1/20) (j : Fin 36) :
    |productWeights w j|≤((1/400:ℚ):ℝ) := by
  dsimp only [productWeights]
  rw [abs_mul]
  convert mul_le_mul (hw (pairLeft j)) (hw (pairRight j)) (abs_nonneg _)
    (by norm_num : (0:ℝ)≤1/20) using 1
  norm_num

theorem first_coarse_bound (w : Fin 8 → ℝ) (hw : ∀ j, |w j|≤1/20)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖firstResponse w t‖≤(firstCoarseRadius:ℝ) := by
  have h := combination_bound first w (fun j => bound (first j)) (r := 1/20)
    (by norm_num) (by simpa using hw) (fun _ => le_rfl) ht
  exact h.trans (by exact_mod_cast first_coarse_checked)

theorem second_coarse_bound (w : Fin 8 → ℝ) (hw : ∀ j, |w j|≤1/20)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖secondResponse w t‖≤(secondCoarseRadius:ℝ) := by
  have h := combination_bound second (productWeights w) (fun j => bound (second j)) (r := 1/400)
    (by norm_num) (product_weights_bound w hw) (fun _ => le_rfl) ht
  exact h.trans (by exact_mod_cast second_coarse_checked)

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unit_gradient_sum {n : ℕ} (k : ℝ) (q : E) (u : Fin n → E) :
    Gravity.unitGradient k q (∑ j, u j)=∑ j, Gravity.unitGradient k q (u j) := by
  simp only [Gravity.unitGradient,inner_sum,Finset.mul_sum,Finset.sum_smul,
    smul_sub,Finset.sum_sub_distrib,Finset.smul_sum]

theorem unit_gradient_smul (k a : ℝ) (q u : E) :
    Gravity.unitGradient k q (a • u)=a • Gravity.unitGradient k q u := by
  simp only [Gravity.unitGradient,inner_smul_right]
  module

theorem unit_hessian_sum_left {n : ℕ} (k : ℝ) (q v : E) (u : Fin n → E) :
    Gravity.unitHessian k q (∑ j, u j) v=∑ j, Gravity.unitHessian k q (u j) v := by
  simp only [Gravity.unitHessian,inner_sum,sum_inner,Finset.mul_sum,Finset.sum_mul,
    Finset.sum_smul,Finset.sum_sub_distrib,Finset.smul_sum,smul_add,Finset.sum_add_distrib]

theorem unit_hessian_symmetric (k : ℝ) (q u v : E) :
    Gravity.unitHessian k q u v=Gravity.unitHessian k q v u := by
  simp only [Gravity.unitHessian,real_inner_comm v u]
  module

theorem unit_hessian_sum_right {n : ℕ} (k : ℝ) (q u : E) (v : Fin n → E) :
    Gravity.unitHessian k q u (∑ j, v j)=∑ j, Gravity.unitHessian k q u (v j) := by
  rw [unit_hessian_symmetric,unit_hessian_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  exact unit_hessian_symmetric k q (v j) u

theorem unit_hessian_smul (k a b : ℝ) (q u v : E) :
    Gravity.unitHessian k q (a • u) (b • v)=(a*b) • Gravity.unitHessian k q u v := by
  simp only [Gravity.unitHessian,inner_smul_right,inner_smul_left,conj_trivial]
  module

theorem unordered_hessian_sum (k : ℝ) (q : E) (u : Fin 8 → E) (w : Fin 8 → ℝ) :
    (∑ j, (productWeights w j*(factor j:ℝ)) •
      Gravity.unitHessian k q (u (pairLeft j)) (u (pairRight j)))=
      (1/2:ℝ) • Gravity.unitHessian k q (∑ j, w j • u j) (∑ j, w j • u j) := by
  rw [unit_hessian_sum_left]
  simp_rw [unit_hessian_sum_right,unit_hessian_smul]
  have hs (i j : Fin 8) (_h : j < i) :
      Gravity.unitHessian k q (u i) (u j)=Gravity.unitHessian k q (u j) (u i) :=
    unit_hessian_symmetric k q (u i) (u j)
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change ((w 0*w 0*(factor 0:ℝ)) • Gravity.unitHessian k q (u 0) (u 0)+
      ((w 0*w 1*(factor 1:ℝ)) • Gravity.unitHessian k q (u 0) (u 1)+
      ((w 0*w 2*(factor 2:ℝ)) • Gravity.unitHessian k q (u 0) (u 2)+
      ((w 0*w 3*(factor 3:ℝ)) • Gravity.unitHessian k q (u 0) (u 3)+
      ((w 0*w 4*(factor 4:ℝ)) • Gravity.unitHessian k q (u 0) (u 4)+
      ((w 0*w 5*(factor 5:ℝ)) • Gravity.unitHessian k q (u 0) (u 5)+
      ((w 0*w 6*(factor 6:ℝ)) • Gravity.unitHessian k q (u 0) (u 6)+
      ((w 0*w 7*(factor 7:ℝ)) • Gravity.unitHessian k q (u 0) (u 7)+
      ((w 1*w 1*(factor 8:ℝ)) • Gravity.unitHessian k q (u 1) (u 1)+
      ((w 1*w 2*(factor 9:ℝ)) • Gravity.unitHessian k q (u 1) (u 2)+
      ((w 1*w 3*(factor 10:ℝ)) • Gravity.unitHessian k q (u 1) (u 3)+
      ((w 1*w 4*(factor 11:ℝ)) • Gravity.unitHessian k q (u 1) (u 4)+
      ((w 1*w 5*(factor 12:ℝ)) • Gravity.unitHessian k q (u 1) (u 5)+
      ((w 1*w 6*(factor 13:ℝ)) • Gravity.unitHessian k q (u 1) (u 6)+
      ((w 1*w 7*(factor 14:ℝ)) • Gravity.unitHessian k q (u 1) (u 7)+
      ((w 2*w 2*(factor 15:ℝ)) • Gravity.unitHessian k q (u 2) (u 2)+
      ((w 2*w 3*(factor 16:ℝ)) • Gravity.unitHessian k q (u 2) (u 3)+
      ((w 2*w 4*(factor 17:ℝ)) • Gravity.unitHessian k q (u 2) (u 4)+
      ((w 2*w 5*(factor 18:ℝ)) • Gravity.unitHessian k q (u 2) (u 5)+
      ((w 2*w 6*(factor 19:ℝ)) • Gravity.unitHessian k q (u 2) (u 6)+
      ((w 2*w 7*(factor 20:ℝ)) • Gravity.unitHessian k q (u 2) (u 7)+
      ((w 3*w 3*(factor 21:ℝ)) • Gravity.unitHessian k q (u 3) (u 3)+
      ((w 3*w 4*(factor 22:ℝ)) • Gravity.unitHessian k q (u 3) (u 4)+
      ((w 3*w 5*(factor 23:ℝ)) • Gravity.unitHessian k q (u 3) (u 5)+
      ((w 3*w 6*(factor 24:ℝ)) • Gravity.unitHessian k q (u 3) (u 6)+
      ((w 3*w 7*(factor 25:ℝ)) • Gravity.unitHessian k q (u 3) (u 7)+
      ((w 4*w 4*(factor 26:ℝ)) • Gravity.unitHessian k q (u 4) (u 4)+
      ((w 4*w 5*(factor 27:ℝ)) • Gravity.unitHessian k q (u 4) (u 5)+
      ((w 4*w 6*(factor 28:ℝ)) • Gravity.unitHessian k q (u 4) (u 6)+
      ((w 4*w 7*(factor 29:ℝ)) • Gravity.unitHessian k q (u 4) (u 7)+
      ((w 5*w 5*(factor 30:ℝ)) • Gravity.unitHessian k q (u 5) (u 5)+
      ((w 5*w 6*(factor 31:ℝ)) • Gravity.unitHessian k q (u 5) (u 6)+
      ((w 5*w 7*(factor 32:ℝ)) • Gravity.unitHessian k q (u 5) (u 7)+
      ((w 6*w 6*(factor 33:ℝ)) • Gravity.unitHessian k q (u 6) (u 6)+
      ((w 6*w 7*(factor 34:ℝ)) • Gravity.unitHessian k q (u 6) (u 7)+
      (w 7*w 7*(factor 35:ℝ)) • Gravity.unitHessian k q (u 7) (u 7))))))))))))))))))))))))))))))))))))=(1/2:ℝ) • (((w 0*w 0) • Gravity.unitHessian k q (u 0) (u 0)+
      ((w 0*w 1) • Gravity.unitHessian k q (u 0) (u 1)+
      ((w 0*w 2) • Gravity.unitHessian k q (u 0) (u 2)+
      ((w 0*w 3) • Gravity.unitHessian k q (u 0) (u 3)+
      ((w 0*w 4) • Gravity.unitHessian k q (u 0) (u 4)+
      ((w 0*w 5) • Gravity.unitHessian k q (u 0) (u 5)+
      ((w 0*w 6) • Gravity.unitHessian k q (u 0) (u 6)+
      (w 0*w 7) • Gravity.unitHessian k q (u 0) (u 7))))))))+
      (((w 1*w 0) • Gravity.unitHessian k q (u 1) (u 0)+
      ((w 1*w 1) • Gravity.unitHessian k q (u 1) (u 1)+
      ((w 1*w 2) • Gravity.unitHessian k q (u 1) (u 2)+
      ((w 1*w 3) • Gravity.unitHessian k q (u 1) (u 3)+
      ((w 1*w 4) • Gravity.unitHessian k q (u 1) (u 4)+
      ((w 1*w 5) • Gravity.unitHessian k q (u 1) (u 5)+
      ((w 1*w 6) • Gravity.unitHessian k q (u 1) (u 6)+
      (w 1*w 7) • Gravity.unitHessian k q (u 1) (u 7))))))))+
      (((w 2*w 0) • Gravity.unitHessian k q (u 2) (u 0)+
      ((w 2*w 1) • Gravity.unitHessian k q (u 2) (u 1)+
      ((w 2*w 2) • Gravity.unitHessian k q (u 2) (u 2)+
      ((w 2*w 3) • Gravity.unitHessian k q (u 2) (u 3)+
      ((w 2*w 4) • Gravity.unitHessian k q (u 2) (u 4)+
      ((w 2*w 5) • Gravity.unitHessian k q (u 2) (u 5)+
      ((w 2*w 6) • Gravity.unitHessian k q (u 2) (u 6)+
      (w 2*w 7) • Gravity.unitHessian k q (u 2) (u 7))))))))+
      (((w 3*w 0) • Gravity.unitHessian k q (u 3) (u 0)+
      ((w 3*w 1) • Gravity.unitHessian k q (u 3) (u 1)+
      ((w 3*w 2) • Gravity.unitHessian k q (u 3) (u 2)+
      ((w 3*w 3) • Gravity.unitHessian k q (u 3) (u 3)+
      ((w 3*w 4) • Gravity.unitHessian k q (u 3) (u 4)+
      ((w 3*w 5) • Gravity.unitHessian k q (u 3) (u 5)+
      ((w 3*w 6) • Gravity.unitHessian k q (u 3) (u 6)+
      (w 3*w 7) • Gravity.unitHessian k q (u 3) (u 7))))))))+
      (((w 4*w 0) • Gravity.unitHessian k q (u 4) (u 0)+
      ((w 4*w 1) • Gravity.unitHessian k q (u 4) (u 1)+
      ((w 4*w 2) • Gravity.unitHessian k q (u 4) (u 2)+
      ((w 4*w 3) • Gravity.unitHessian k q (u 4) (u 3)+
      ((w 4*w 4) • Gravity.unitHessian k q (u 4) (u 4)+
      ((w 4*w 5) • Gravity.unitHessian k q (u 4) (u 5)+
      ((w 4*w 6) • Gravity.unitHessian k q (u 4) (u 6)+
      (w 4*w 7) • Gravity.unitHessian k q (u 4) (u 7))))))))+
      (((w 5*w 0) • Gravity.unitHessian k q (u 5) (u 0)+
      ((w 5*w 1) • Gravity.unitHessian k q (u 5) (u 1)+
      ((w 5*w 2) • Gravity.unitHessian k q (u 5) (u 2)+
      ((w 5*w 3) • Gravity.unitHessian k q (u 5) (u 3)+
      ((w 5*w 4) • Gravity.unitHessian k q (u 5) (u 4)+
      ((w 5*w 5) • Gravity.unitHessian k q (u 5) (u 5)+
      ((w 5*w 6) • Gravity.unitHessian k q (u 5) (u 6)+
      (w 5*w 7) • Gravity.unitHessian k q (u 5) (u 7))))))))+
      (((w 6*w 0) • Gravity.unitHessian k q (u 6) (u 0)+
      ((w 6*w 1) • Gravity.unitHessian k q (u 6) (u 1)+
      ((w 6*w 2) • Gravity.unitHessian k q (u 6) (u 2)+
      ((w 6*w 3) • Gravity.unitHessian k q (u 6) (u 3)+
      ((w 6*w 4) • Gravity.unitHessian k q (u 6) (u 4)+
      ((w 6*w 5) • Gravity.unitHessian k q (u 6) (u 5)+
      ((w 6*w 6) • Gravity.unitHessian k q (u 6) (u 6)+
      (w 6*w 7) • Gravity.unitHessian k q (u 6) (u 7))))))))+
      ((w 7*w 0) • Gravity.unitHessian k q (u 7) (u 0)+
      ((w 7*w 1) • Gravity.unitHessian k q (u 7) (u 1)+
      ((w 7*w 2) • Gravity.unitHessian k q (u 7) (u 2)+
      ((w 7*w 3) • Gravity.unitHessian k q (u 7) (u 3)+
      ((w 7*w 4) • Gravity.unitHessian k q (u 7) (u 4)+
      ((w 7*w 5) • Gravity.unitHessian k q (u 7) (u 5)+
      ((w 7*w 6) • Gravity.unitHessian k q (u 7) (u 6)+
      (w 7*w 7) • Gravity.unitHessian k q (u 7) (u 7)))))))))))))))
  norm_num only [show factor 0=(1/2:ℚ) from by decide +kernel,
    show factor 1=(1:ℚ) from by decide +kernel,
    show factor 2=(1:ℚ) from by decide +kernel,
    show factor 3=(1:ℚ) from by decide +kernel,
    show factor 4=(1:ℚ) from by decide +kernel,
    show factor 5=(1:ℚ) from by decide +kernel,
    show factor 6=(1:ℚ) from by decide +kernel,
    show factor 7=(1:ℚ) from by decide +kernel,
    show factor 8=(1/2:ℚ) from by decide +kernel,
    show factor 9=(1:ℚ) from by decide +kernel,
    show factor 10=(1:ℚ) from by decide +kernel,
    show factor 11=(1:ℚ) from by decide +kernel,
    show factor 12=(1:ℚ) from by decide +kernel,
    show factor 13=(1:ℚ) from by decide +kernel,
    show factor 14=(1:ℚ) from by decide +kernel,
    show factor 15=(1/2:ℚ) from by decide +kernel,
    show factor 16=(1:ℚ) from by decide +kernel,
    show factor 17=(1:ℚ) from by decide +kernel,
    show factor 18=(1:ℚ) from by decide +kernel,
    show factor 19=(1:ℚ) from by decide +kernel,
    show factor 20=(1:ℚ) from by decide +kernel,
    show factor 21=(1/2:ℚ) from by decide +kernel,
    show factor 22=(1:ℚ) from by decide +kernel,
    show factor 23=(1:ℚ) from by decide +kernel,
    show factor 24=(1:ℚ) from by decide +kernel,
    show factor 25=(1:ℚ) from by decide +kernel,
    show factor 26=(1/2:ℚ) from by decide +kernel,
    show factor 27=(1:ℚ) from by decide +kernel,
    show factor 28=(1:ℚ) from by decide +kernel,
    show factor 29=(1:ℚ) from by decide +kernel,
    show factor 30=(1/2:ℚ) from by decide +kernel,
    show factor 31=(1:ℚ) from by decide +kernel,
    show factor 32=(1:ℚ) from by decide +kernel,
    show factor 33=(1/2:ℚ) from by decide +kernel,
    show factor 34=(1:ℚ) from by decide +kernel,
    show factor 35=(1/2:ℚ) from by decide +kernel,
    Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,mul_one]
  simp only [hs 1 0 (by decide),
    hs 2 0 (by decide),
    hs 2 1 (by decide),
    hs 3 0 (by decide),
    hs 3 1 (by decide),
    hs 3 2 (by decide),
    hs 4 0 (by decide),
    hs 4 1 (by decide),
    hs 4 2 (by decide),
    hs 4 3 (by decide),
    hs 5 0 (by decide),
    hs 5 1 (by decide),
    hs 5 2 (by decide),
    hs 5 3 (by decide),
    hs 5 4 (by decide),
    hs 6 0 (by decide),
    hs 6 1 (by decide),
    hs 6 2 (by decide),
    hs 6 3 (by decide),
    hs 6 4 (by decide),
    hs 6 5 (by decide),
    hs 7 0 (by decide),
    hs 7 1 (by decide),
    hs 7 2 (by decide),
    hs 7 3 (by decide),
    hs 7 4 (by decide),
    hs 7 5 (by decide),
    hs 7 6 (by decide)]
  module

end Algebra
end GNC.OrbitalComparison.CenteredResponseData
