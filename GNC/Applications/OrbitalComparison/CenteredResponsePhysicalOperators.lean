import GNC.Applications.OrbitalComparison.CenteredResponseDefect

/-! Uniform assembled residuals against the derivatives of the exact
inverse-square field. The first-response force hypothesis isolates the
remaining rotation-family substitution. These are response-equation
certificates, not yet a bound for a nonlinear physical orbit. -/
noncomputable section
namespace GNC.OrbitalComparison.CenteredResponseData
open CartesianResponsePolynomial Matrix Set

theorem gradient_error_nonnegative : (0:ℝ)≤gradientError := by norm_num [gradientError]
theorem hessian_error_nonnegative : (0:ℝ)≤halfHessianError := by norm_num [halfHessianError]

theorem first_physical_operator_defect (w : Fin 8 → ℝ) (hw : ∀ j, |w j|≤1/20)
    (du : E3) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hu : ‖du-response sources w t‖≤(1/20)*(forceFactor:ℝ)*(phaseError:ℝ)) :
    ‖firstAcceleration w t-(Gravity.gradient (K:ℝ) (nominal t) (firstResponse w t)+du)‖≤
      (firstDefect:ℝ) := by
  have hg := (gradient_transfer (firstResponse w t) ht).trans
    (mul_le_mul_of_nonneg_left (first_coarse_bound w hw ht) gradient_error_nonnegative)
  have he : firstAcceleration w t-(Gravity.gradient (K:ℝ) (nominal t) (firstResponse w t)+du)=
      (firstAcceleration w t-(Gravity.unitGradient (K:ℝ) (polynomialNominal t)
        (firstResponse w t)+response sources w t))-
      (Gravity.gradient (K:ℝ) (nominal t) (firstResponse w t)-
        Gravity.unitGradient (K:ℝ) (polynomialNominal t) (firstResponse w t))-
      (du-response sources w t) := by module
  have hb : (linearDefect:ℝ)+(gradientError:ℝ)*(firstCoarseRadius:ℝ)+
      (1/20)*(forceFactor:ℝ)*(phaseError:ℝ)≤(firstDefect:ℝ) := by
    have hbq : linearDefect+gradientError*firstCoarseRadius+
        (1/20)*forceFactor*phaseError≤firstDefect := by
      simpa only [linear_budget_checked] using first_transfer_budget_checked
    have hcast := (Rat.cast_le (K := ℝ)).mpr hbq
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hcast
  rw [he]
  exact ((norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add (first_surrogate_defect w hw ht) hg)) hu)).trans hb

theorem second_physical_operator_defect (w : Fin 8 → ℝ) (hw : ∀ j, |w j|≤1/20)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖secondAcceleration w t-(Gravity.gradient (K:ℝ) (nominal t) (secondResponse w t)+
      (1/2:ℝ) • Gravity.hessian (K:ℝ) (nominal t) (firstResponse w t) (firstResponse w t))‖≤
      (secondDefect:ℝ) := by
  have hg := (gradient_transfer (secondResponse w t) ht).trans
    (mul_le_mul_of_nonneg_left (second_coarse_bound w hw ht) gradient_error_nonnegative)
  have hy := first_coarse_bound w hw ht
  have hh := half_hessian_transfer (firstResponse w t) (firstResponse w t) ht
  have hh' : ‖(1/2:ℝ) • (Gravity.hessian (K:ℝ) (nominal t) (firstResponse w t) (firstResponse w t)-
      Gravity.unitHessian (K:ℝ) (polynomialNominal t) (firstResponse w t) (firstResponse w t))‖≤
      (halfHessianError:ℝ)*(firstCoarseRadius:ℝ)^2 := by
    apply hh.trans
    calc
      _=(halfHessianError:ℝ)*‖firstResponse w t‖^2 := by ring
      _≤_ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hy 2) hessian_error_nonnegative
  have he : secondAcceleration w t-
      (Gravity.gradient (K:ℝ) (nominal t) (secondResponse w t)+
        (1/2:ℝ) • Gravity.hessian (K:ℝ) (nominal t) (firstResponse w t) (firstResponse w t))=
      (secondAcceleration w t-(Gravity.unitGradient (K:ℝ) (polynomialNominal t)
        (secondResponse w t)+(1/2:ℝ) • Gravity.unitHessian (K:ℝ) (polynomialNominal t)
          (firstResponse w t) (firstResponse w t)))-
      (Gravity.gradient (K:ℝ) (nominal t) (secondResponse w t)-
        Gravity.unitGradient (K:ℝ) (polynomialNominal t) (secondResponse w t))-
      (1/2:ℝ) • (Gravity.hessian (K:ℝ) (nominal t) (firstResponse w t) (firstResponse w t)-
        Gravity.unitHessian (K:ℝ) (polynomialNominal t) (firstResponse w t) (firstResponse w t)) := by
    module
  have hb : (quadraticDefect:ℝ)+(gradientError:ℝ)*(secondCoarseRadius:ℝ)+
      (halfHessianError:ℝ)*(firstCoarseRadius:ℝ)^2≤(secondDefect:ℝ) := by
    exact_mod_cast (show quadraticDefect+gradientError*secondCoarseRadius+
        halfHessianError*firstCoarseRadius^2≤secondDefect by
      simpa only [quadratic_budget_checked] using second_transfer_budget_checked)
  rw [he]
  exact ((norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add (second_surrogate_defect w hw ht) hg)) hh')).trans hb

end GNC.OrbitalComparison.CenteredResponseData
