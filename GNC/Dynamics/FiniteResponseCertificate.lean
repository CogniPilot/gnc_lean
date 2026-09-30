import GNC.Dynamics.RetainedMonomialCertificate

/-! Certificates for finite linear-response candidates. Their differential
residual is charged with its time profile. No exact-response solution or
numerical integration tolerance is substituted for that residual. -/
noncomputable section
namespace GNC.Gravity
open Set Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The candidate's radius follows from its defining derivatives and checked
residual. It need not solve the retained ODE exactly. -/
theorem response_shape_of_defect (μ r F ε : ℝ) (n : ℕ)
    (hμ : 0≤μ) (hr : 0<r) (hF : 0≤F) (hε : 0≤ε) (hk : 2*μ/r^3<56)
    (q y yv ya du : ℝ → E)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r≤‖q t‖)
    (hu : ∀ t ∈ Icc (0:ℝ) 1, ‖du t‖≤F)
    (hdef : ∀ t ∈ Icc (0:ℝ) 1, ‖gradient μ (q t) (y t)+du t-ya t‖≤ε*t^n)
    (hy : Continuous y) (hyv : Continuous yv)
    (hdy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt y (yv t) t)
    (hdyv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt yv (ya t) t)
    (hi : y 0=0) (hiv : yv 0=0) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖y t‖≤((F+ε)*PolynomialSupersolution.value (2*μ/r^3) 1)*t^2 := by
  apply retained_response_shape μ r (F+ε) hμ hr (add_nonneg hF hε) hk q y yv
    (fun t => ya t-gradient μ (q t) (y t)) hq ?_ hy hyv hdy ?_ hi hiv
  · intro t ht
    have he : ya t-gradient μ (q t) (y t) =
        du t-(gradient μ (q t) (y t)+du t-ya t) := by abel
    change ‖ya t-gradient μ (q t) (y t)‖≤F+ε
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (hu t ht)
      ((hdef t ht).trans (mul_le_of_le_one_right hε (pow_le_one₀ ht.1 ht.2))))
  · intro t ht
    simpa using hdyv t ht

theorem retained_finite_prediction (μ r L δ ε κ : ℝ) (n : ℕ)
    (hμ : 0≤μ) (hL : 0≤L) (hregion : 2*L<r) (hδ : 0≤δ) (hε : 0≤ε)
    (hκ : 0≤κ) (hk : κ<56) (hlip : 2*μ/(r-2*L)^3≤κ)
    (hclose : (δ+ε+3*μ/(r-L)^4*L^2)*PolynomialSupersolution.value κ 1<L)
    (x xv q qv y yv ya u du : ℝ → E)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r≤‖q t‖)
    (hybound : ∀ t ∈ Icc (0:ℝ) 1, ‖y t‖≤L*t^2)
    (hdef : ∀ t ∈ Icc (0:ℝ) 1, ‖gradient μ (q t) (y t)+du t-ya t‖≤δ+ε*t^n)
    (hx : Continuous x) (hxv : Continuous xv) (hcq : Continuous q) (hcqv : Continuous qv)
    (hy : Continuous y) (hyv : Continuous yv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (field μ (x t)+(u t+du t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (field μ (q t)+u t) t)
    (hdy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt y (yv t) t)
    (hdyv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt yv (ya t) t)
    (hip : x 0=q 0+y 0) (hiv : xv 0=qv 0+yv 0) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖x t-(q t+y t)‖≤δ*MonomialSupersolution.value κ 0 t+ε*MonomialSupersolution.value κ n t+
        (3*μ/(r-L)^4*L^2)*MonomialSupersolution.value κ 4 t ∧
      ‖xv t-(qv t+yv t)‖≤δ*MonomialSupersolution.velocity κ 0 t+ε*MonomialSupersolution.velocity κ n t+
        (3*μ/(r-L)^4*L^2)*MonomialSupersolution.velocity κ 4 t := by
  have h := monomial_prediction μ hμ x xv (fun t => q t+y t) (fun t => qv t+yv t)
    (fun t => field μ (q t)+u t+ya t)
    (fun t => u t+du t) ![δ, ε, 3*μ/(r-L)^4*L^2] ![0,n,4]
    hκ hk (by intro i; fin_cases i <;> dsimp <;> positivity)
    (show 0<r-2*L by linarith) (by simpa [Fin.sum_univ_succ, add_assoc] using hclose) hlip (by
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
      have he : field μ (q t+y t)+(u t+du t)-
          (field μ (q t)+u t+ya t)=
          (gradient μ (q t) (y t)+du t-ya t)+(field μ (q t+y t)-field μ (q t)-gradient μ (q t) (y t)) := by module
      rw [he]
      apply (norm_add_le _ _).trans
      have hg' := hg.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hybound t ht) 2) (by positivity : 0≤3*μ/(r-L)^4))
      convert add_le_add (hdef t ht) hg' using 1
      simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, pow_zero, mul_one, Fin.sum_univ_zero, add_zero]
      ring)
  simpa [Fin.sum_univ_succ, add_assoc] using h

end GNC.Gravity
