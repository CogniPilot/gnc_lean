import GNC.Dynamics.LieRadiusSpatialApproximation

/-! Low-degree checking of the exact Lie translation radius. The delivered
Jacobian remains exact. Its projection is checked with a quadratic skew
polynomial, while the Gram term uses a separate sharp norm-distortion
bound. This avoids squaring a high-degree reconstructed trajectory. -/
noncomputable section
namespace GNC.LieRadiusQuadratic
open Matrix Real Set

def apply (φ v : Vec3) : Vec3 := v+(1/2:ℝ) • (φ ⨯₃ v)+(1/6:ℝ) • (φ ⨯₃ (φ ⨯₃ v))
def tail (s : ℝ) : ℝ := s^3/24+s^4/120

theorem tail_nonnegative {s : ℝ} (hs : 0≤s) : 0≤tail s := by unfold tail; positivity
theorem tail_mono {s t : ℝ} (hs : 0≤s) (hst : s≤t) : tail s≤tail t := by unfold tail; gcongr

private theorem cosine_taylor (x : ℝ) : taylorWithinEval cos 3 univ 0 x=1-x^2/2 := by
  norm_num [taylorWithinEval_succ,iteratedDerivWithin_univ,iteratedDeriv_succ,
    Real.deriv_sin,deriv_cos',deriv.neg',deriv_neg]
  ring
private theorem sine_taylor (x : ℝ) : taylorWithinEval sin 4 univ 0 x=x-x^3/6 := by
  norm_num [taylorWithinEval_succ,iteratedDerivWithin_univ,iteratedDeriv_succ,
    Real.deriv_sin,deriv_cos',deriv.neg',deriv_neg]
  ring

theorem cosine_bound {x : ℝ} (hx : 0≤x) : |1-cos x-x^2/2|≤x^4/24 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x; norm_num
  · have h := TrigonometricPolynomial.taylor_bound_pos cos contDiff_cos 3
      (abs_iteratedDeriv_cos_le_one 4) hp
    rw [cosine_taylor] at h
    have he : 1-cos x-x^2/2= -(cos x-(1-x^2/2)) := by ring
    rw [he,abs_neg]
    simpa using h

theorem sine_bound {x : ℝ} (hx : 0≤x) : |(x-x^3/6)-sin x|≤x^5/120 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x; norm_num
  · have h := TrigonometricPolynomial.taylor_bound_pos sin contDiff_sin 4
      (abs_iteratedDeriv_sin_le_one 5) hp
    rw [sine_taylor,abs_sub_comm] at h
    simpa using h

theorem error_bound (φ v : Vec3) : enorm (Jacobian.leftAt φ v-apply φ v)≤tail (enorm φ)*enorm v := by
  by_cases hz : enorm φ=0
  · rw [(enorm_eq_zero_iff φ).mp hz]
    have h0 : enorm (0:Vec3)=0 := (enorm_eq_zero_iff _).mpr rfl
    simp [Jacobian.leftAt,apply,h0,tail]
  · have hp : 0<enorm φ := lt_of_le_of_ne (enorm_nonneg φ) (Ne.symm hz)
    have ha : |(1-cos (enorm φ)-(enorm φ)^2/2)/(enorm φ)^2|≤(enorm φ)^2/24 := by
      simp only [abs_div,abs_pow,abs_of_nonneg hp.le]
      apply (div_le_div_of_nonneg_right (cosine_bound hp.le) (sq_nonneg _)).trans_eq
      field_simp
    have hb : |((enorm φ-(enorm φ)^3/6)-sin (enorm φ))/(enorm φ)^3|≤(enorm φ)^2/120 := by
      simp only [abs_div,abs_pow,abs_of_nonneg hp.le]
      apply (div_le_div_of_nonneg_right (sine_bound hp.le) (pow_nonneg hp.le 3)).trans_eq
      field_simp
    have h1 : (1-cos (enorm φ))/(enorm φ)^2-1/2=
        (1-cos (enorm φ)-(enorm φ)^2/2)/(enorm φ)^2 := by field_simp
    have h2 : (enorm φ-sin (enorm φ))/(enorm φ)^3-1/6=
        ((enorm φ-(enorm φ)^3/6)-sin (enorm φ))/(enorm φ)^3 := by field_simp <;> ring
    have he : Jacobian.leftAt φ v-apply φ v=
        ((1-cos (enorm φ)-(enorm φ)^2/2)/(enorm φ)^2) • (φ ⨯₃ v)+
        (((enorm φ-(enorm φ)^3/6)-sin (enorm φ))/(enorm φ)^3) • (φ ⨯₃ (φ ⨯₃ v)) := by
      rw [←h1,←h2]
      simp only [Jacobian.leftAt,apply]
      module
    have hn1 := cross_enorm_le φ v
    have hn2 := (cross_enorm_le φ (φ ⨯₃ v)).trans (mul_le_mul_of_nonneg_left hn1 hp.le)
    rw [he]
    apply (enorm_add_le _ _).trans
    rw [enorm_smul,enorm_smul]
    convert add_le_add (mul_le_mul ha hn1 (enorm_nonneg _) (by positivity))
      (mul_le_mul hb hn2 (enorm_nonneg _) (by positivity)) using 1 <;> dsimp [tail] <;> ring

/-- The exact Jacobian's squared norm differs from the input squared norm
by at most theta^2/12 times that norm. No Taylor polynomial for the squared
Jacobian is needed, and zero rotation is included. -/
theorem norm_distortion (φ v : Vec3) :
    |enorm (Jacobian.leftAt φ v)^2-enorm v^2|≤(enorm φ)^2/12*enorm v^2 := by
  by_cases hz : enorm φ=0
  · rw [(enorm_eq_zero_iff φ).mp hz]
    simp [Jacobian.leftAt]
    positivity
  · have hp : 0<enorm φ := lt_of_le_of_ne (enorm_nonneg φ) (Ne.symm hz)
    have hc := cosine_bound hp.le
    have hcoeff : ((1-cos (enorm φ))/(enorm φ)^2)^2-
        2*((enorm φ-sin (enorm φ))/(enorm φ)^3)+
        (enorm φ)^2*((enorm φ-sin (enorm φ))/(enorm φ)^3)^2=
        2*(1-cos (enorm φ)-(enorm φ)^2/2)/(enorm φ)^4 := by
      field_simp
      nlinarith [sin_sq_add_cos_sq (enorm φ)]
    have hb : |2*(1-cos (enorm φ)-(enorm φ)^2/2)/(enorm φ)^4|≤1/12 := by
      rw [abs_div,abs_mul,abs_pow,abs_of_nonneg hp.le]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num))
        (pow_nonneg hp.le 4)).trans_eq
      field_simp <;> norm_num
    have hg := JacobianPolynomial.gram φ v ((1-cos (enorm φ))/(enorm φ)^2)
      ((enorm φ-sin (enorm φ))/(enorm φ)^3)
    rw [←enorm_sq,hcoeff] at hg
    change enorm (Jacobian.leftAt φ v)^2=_ at hg
    rw [hg,add_sub_cancel_left,abs_mul,abs_of_nonneg (sq_nonneg (enorm (φ ⨯₃ v)))]
    have hn := pow_le_pow_left₀ (enorm_nonneg _) (cross_enorm_le φ v) 2
    convert mul_le_mul hb hn (sq_nonneg _) (by norm_num : (0:ℝ)≤1/12) using 1 <;> ring

def radiusApprox (q qhat φ ρ : Vec3) : ℝ :=
  enorm q^2+2*(qhat ⬝ᵥ apply φ ρ)+enorm ρ^2

theorem radius_error (q qhat φ ρ : Vec3) {σ P δ : ℝ}
    (hφ : enorm φ<2*π) (hσ : enorm φ≤σ) (hρ : enorm ρ≤P)
    (hq : enorm (q-qhat)≤δ) :
    |enorm (q+Jacobian.leftAt φ ρ)^2-radiusApprox q qhat φ ρ|≤
      2*δ*(1+tail σ)*P+2*enorm q*tail σ*P+σ^2/12*P^2 := by
  have hσ0 := (enorm_nonneg φ).trans hσ
  have hP0 := (enorm_nonneg ρ).trans hρ
  have hδ0 := (enorm_nonneg _).trans hq
  have hd := (leftAt_nonexpansive φ ρ hφ).trans hρ
  have he : enorm (Jacobian.leftAt φ ρ-apply φ ρ)≤tail σ*P :=
    (error_bound φ ρ).trans
      (mul_le_mul (tail_mono (enorm_nonneg φ) hσ) hρ (enorm_nonneg _) (tail_nonnegative hσ0))
  have hap : enorm (apply φ ρ)≤(1+tail σ)*P := by
    have hi : apply φ ρ=Jacobian.leftAt φ ρ-(Jacobian.leftAt φ ρ-apply φ ρ) := by module
    rw [hi]
    have h := enorm_add_le (Jacobian.leftAt φ ρ) (-(Jacobian.leftAt φ ρ-apply φ ρ))
    rw [enorm_neg] at h
    exact h.trans ((add_le_add hd he).trans_eq (by ring))
  have hg : |enorm (Jacobian.leftAt φ ρ)^2-enorm ρ^2|≤σ^2/12*P^2 :=
    (norm_distortion φ ρ).trans (by gcongr <;> exact enorm_nonneg _)
  have h1 := (LieRadiusApproximation.abs_dot_bound (q-qhat) (apply φ ρ)).trans
    (mul_le_mul hq hap (enorm_nonneg _) hδ0)
  have h2 := (LieRadiusApproximation.abs_dot_bound q (Jacobian.leftAt φ ρ-apply φ ρ)).trans
    (mul_le_mul_of_nonneg_left he (enorm_nonneg q))
  have hi : enorm (q+Jacobian.leftAt φ ρ)^2-radiusApprox q qhat φ ρ=
      2*((q-qhat) ⬝ᵥ apply φ ρ)+2*(q ⬝ᵥ (Jacobian.leftAt φ ρ-apply φ ρ))+
      (enorm (Jacobian.leftAt φ ρ)^2-enorm ρ^2) := by
    simp only [radiusApprox,enorm_sq,←dot_self_lengthSq,add_dotProduct,dotProduct_add,
      sub_dotProduct,dotProduct_sub,dotProduct_comm (Jacobian.leftAt φ ρ) q]
    ring
  rw [hi]
  apply (abs_add_le _ _).trans
  apply add_le_add _ hg
  apply (abs_add_le _ _).trans
  norm_num only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  convert add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ)≤2))
    (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ)≤2)) using 1 <;> ring

/-- Zero-initial-error translations often have a checked quadratic growth
profile. Preserve that time dependence in the scalar radius check instead
of replacing it with the endpoint radius error throughout the burn. -/
theorem radius_error_growth (q qhat φ ρ : Vec3) (t : ℝ) {σ Z δ : ℝ}
    (hφ : enorm φ<2*π) (hσ : enorm φ≤σ) (hρ : enorm ρ≤Z*t^2)
    (hq : enorm (q-qhat)≤δ) :
    |enorm (q+Jacobian.leftAt φ ρ)^2-radiusApprox q qhat φ ρ|≤
      (2*δ*(1+tail σ)*Z+2*enorm q*tail σ*Z)*t^2+
        (σ^2/12*Z^2)*t^4 := by
  convert radius_error q qhat φ ρ hφ hσ hρ hq using 1 <;> ring

end GNC.LieRadiusQuadratic
