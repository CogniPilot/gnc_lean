import GNC.Dynamics.MonomialOrbitCertificate
import GNC.Dynamics.GravityRemainderBall
import GNC.Analysis.ConstantSecondOrderBound

/-! The same time-profile certificate for Cartesian variational predictors.
An exact-component response has zero input approximation budget; an angle
STM pays its rigorously bounded rotation remainder. Both pay the identical
quadratic spatial-gravity remainder and use the same region-closing proof.
-/
noncomputable section
namespace GNC.Gravity
open Set Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem retained_response_shape (μ r F : ℝ) (hμ : 0≤μ) (hr : 0<r)
    (hF : 0≤F) (hk : 2*μ/r^3<56) (q y yv du : ℝ → E)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r≤‖q t‖)
    (hu : ∀ t ∈ Icc (0:ℝ) 1, ‖du t‖≤F)
    (hy : Continuous y) (hyv : Continuous yv)
    (hdy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt y (yv t) t)
    (hdyv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt yv (gradient μ (q t) (y t)+du t) t)
    (hi : y 0=0) (hiv : yv 0=0) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖y t‖≤(F*PolynomialSupersolution.value (2*μ/r^3) 1)*t^2 := by
  have hk0 : 0≤2*μ/r^3 := by positivity
  have h := ConstantSecondOrderBound.response y yv (fun t => gradient μ (q t) (y t)+du t)
    hk0 hk hF hy hyv hdy hdyv hi hiv (by
      intro t ht
      have hg := gradient_bound μ hμ (q t) (y t)
      have hg' := hg.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hr.le (hq t ht) 3)) (norm_nonneg _))
      exact (norm_add_le _ _).trans (add_le_add hg' (hu t ht)))
  intro t ht
  exact (h t ht).1.trans ((mul_le_mul_of_nonneg_left
    (PolynomialSupersolution.quadratic_shape hk0 hk ht) hF).trans_eq (by ring))

theorem retained_monomial_prediction (μ r L ε κ : ℝ)
    (hμ : 0≤μ) (hL : 0≤L) (hregion : 2*L<r) (hε : 0≤ε)
    (hκ : 0≤κ) (hk : κ<56) (hlip : 2*μ/(r-2*L)^3≤κ)
    (hclose : (ε+3*μ/(r-L)^4*L^2)*PolynomialSupersolution.value κ 1<L)
    (x xv q qv y yv u du actualDu : ℝ → E)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r≤‖q t‖)
    (hybound : ∀ t ∈ Icc (0:ℝ) 1, ‖y t‖≤L*t^2)
    (hinput : ∀ t ∈ Icc (0:ℝ) 1, ‖actualDu t-du t‖≤ε)
    (hx : Continuous x) (hxv : Continuous xv) (hcq : Continuous q) (hcqv : Continuous qv)
    (hy : Continuous y) (hyv : Continuous yv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (field μ (x t)+(u t+actualDu t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (field μ (q t)+u t) t)
    (hdy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt y (yv t) t)
    (hdyv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt yv (gradient μ (q t) (y t)+du t) t)
    (hip : x 0=q 0+y 0) (hiv : xv 0=qv 0+yv 0) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖x t-(q t+y t)‖≤ε*MonomialSupersolution.value κ 0 t+
        (3*μ/(r-L)^4*L^2)*MonomialSupersolution.value κ 4 t ∧
      ‖xv t-(qv t+yv t)‖≤ε*MonomialSupersolution.velocity κ 0 t+
        (3*μ/(r-L)^4*L^2)*MonomialSupersolution.velocity κ 4 t := by
  have h := monomial_prediction μ hμ x xv (fun t => q t+y t) (fun t => qv t+yv t)
    (fun t => field μ (q t)+u t+(gradient μ (q t) (y t)+du t))
    (fun t => u t+actualDu t) ![ε, 3*μ/(r-L)^4*L^2] ![0,4]
    hκ hk (by intro i; fin_cases i; exact hε; dsimp; positivity)
    (show 0<r-2*L by linarith) (by simpa [Fin.sum_univ_two] using hclose) hlip (by
      intro t ht
      have hyL := (hybound t ht).trans (mul_le_of_le_one_right hL (pow_le_one₀ ht.1 ht.2))
      have hn := norm_sub_norm_le (q t) (-y t)
      have hqt := hq t ht
      simp only [norm_neg, sub_neg_eq_add] at hn
      linarith)
    hx hxv (hcq.add hy) (hcqv.add hyv) hdx hdxv
    (fun t ht => (hdq t ht).add (hdy t ht))
    (fun t ht => (hdqv t ht).add (hdyv t ht)) hip hiv (by
      intro t ht
      have hyL := (hybound t ht).trans (mul_le_of_le_one_right hL (pow_le_one₀ ht.1 ht.2))
      have hg := remainder_quadratic μ hμ (q t) (y t) (show L<r by linarith) (hq t ht) hyL
      have he : field μ (q t+y t)+(u t+actualDu t)-
          (field μ (q t)+u t+(gradient μ (q t) (y t)+du t))=
          (actualDu t-du t)+(field μ (q t+y t)-field μ (q t)-gradient μ (q t) (y t)) := by module
      rw [he]
      apply (norm_add_le _ _).trans
      have hg' := hg.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hybound t ht) 2) (by positivity : 0≤3*μ/(r-L)^4))
      convert add_le_add (hinput t ht) hg' using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, mul_one]
      ring)
  simpa [Fin.sum_univ_two] using h

end GNC.Gravity
