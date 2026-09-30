import GNC.Dynamics.ClassicalOrbitEquivalence

/-! Elliptic Kepler coefficients and the physical-time/true-anomaly clock.
No frozen angular rate or omitted angular acceleration is used. -/
noncomputable section
open Matrix Real
namespace GNC.KeplerAnomaly
open ClassicalOrbitEquivalence RadialGravityFrame RotatingVariational

def kappa (e f : ℝ) : ℝ := 1+e*cos f
def kappaPrime (e f : ℝ) : ℝ := -e*sin f
def rate (e h p f : ℝ) : ℝ := h*(kappa e f)^2/p^2
def radius (e p f : ℝ) : ℝ := p/kappa e f

theorem kappa_pos {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) (f : ℝ) :
    0 < kappa e f := by
  have hc := mul_le_mul_of_nonneg_left (neg_one_le_cos f) he
  dsimp [kappa]
  nlinarith

theorem rate_pos {e h p : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hh : 0 < h) (hp : 0 < p) (f : ℝ) : 0 < rate e h p f := by
  unfold rate
  exact div_pos (mul_pos hh (sq_pos_of_pos (kappa_pos he he1 f))) (sq_pos_of_pos hp)

theorem radius_pos {e p : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hp : 0 < p) (f : ℝ) : 0 < radius e p f :=
  div_pos hp (kappa_pos he he1 f)

theorem omega_derivative {w : ℝ → ℝ} {d t : ℝ} (hw : HasDerivAt w d t) :
    HasDerivAt (fun s => omega (w s)) (omega d) t := by
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  fin_cases i <;> fin_cases j <;>
    first
    | simpa [omega, skew, Matrix.cons_val_two] using hw
    | simpa [omega, skew, Matrix.cons_val_two] using hw.neg
    | simpa [omega, skew, Matrix.cons_val_two] using hasDerivAt_const t (0 : ℝ)

theorem gravity_coefficient {e h p μ : ℝ} (hp : p ≠ 0)
    (hKepler : h^2 = μ*p) (f : ℝ) :
    μ/(radius e p f)^3 = (rate e h p f)^2/kappa e f := by
  by_cases hk : kappa e f = 0
  · simp [radius, rate, hk]
  · have hm : μ = h^2/p := by field_simp; nlinarith [hKepler]
    rw [hm]
    simp only [radius, rate]
    field_simp <;> ring

/-- Kepler's areal clock gives the exact coefficients needed for TH. -/
theorem coefficient_derivatives {e h p : ℝ} {f : ℝ → ℝ} {t : ℝ}
    (hp : p ≠ 0) (hk : kappa e (f t) ≠ 0)
    (hf : HasDerivAt f (rate e h p (f t)) t) :
    HasDerivAt (fun s => kappa e (f s))
      (rate e h p (f t)*kappaPrime e (f t)) t ∧
    HasDerivAt (fun s => kappaPrime e (f s))
      (rate e h p (f t)*(1-kappa e (f t))) t ∧
    HasDerivAt (fun s => rate e h p (f s))
      (2*(rate e h p (f t))^2*kappaPrime e (f t)/kappa e (f t)) t := by
  have hd : HasDerivAt (fun s => kappa e (f s))
      (rate e h p (f t)*kappaPrime e (f t)) t := by
    convert ((hf.cos).const_mul e).const_add 1 using 1
    simp [kappaPrime]; ring
  refine ⟨hd, ?_, ?_⟩
  · convert (hf.sin).const_mul (-e) using 1
    simp [kappa]; ring
  · convert ((hd.pow 2).const_mul h).div_const (p^2) using 1
    simp only [rate, kappaPrime]
    field_simp <;> ring

/-- This theorem connects the actual inverse-square coefficient μ/r³
and the Kepler clock to the time-rescaled TH differential equation. -/
theorem kepler_to_th {e h p μ : ℝ} {f : ℝ → ℝ} {F : ℝ → M6} {t : ℝ}
    (he : 0 ≤ e) (he1 : e < 1) (hh : 0 < h) (hp : 0 < p)
    (hKepler : h^2 = μ*p)
    (hf : HasDerivAt f (rate e h p (f t)) t)
    (hF : HasDerivAt F
      (classicalGenerator (gravity (μ/(radius e p (f t))^3))
        (omega (rate e h p (f t)))
        (omega (2*(rate e h p (f t))^2*kappaPrime e (f t)/kappa e (f t))) * F t) t) :
    HasDerivAt (fun s => anomalyChange (kappa e (f s)) (kappaPrime e (f s))
        (rate e h p (f s)) * F s)
      ((rate e h p (f t) • th (kappa e (f t))) *
        (anomalyChange (kappa e (f t)) (kappaPrime e (f t)) (rate e h p (f t)) * F t)) t := by
  have hk := (kappa_pos he he1 (f t)).ne'
  obtain ⟨hkd,hpd,hwd⟩ := coefficient_derivatives hp.ne' hk hf
  apply to_th (k := fun s => kappa e (f s))
    (kp := fun s => kappaPrime e (f s)) (w := fun s => rate e h p (f s))
    (t := t) hk (rate_pos he he1 hh hp (f t)).ne' hkd hpd hwd
  simpa only [gravity_coefficient hp.ne' hKepler] using hF

end GNC.KeplerAnomaly
