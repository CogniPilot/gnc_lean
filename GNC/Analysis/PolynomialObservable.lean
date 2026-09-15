import GNC.Analysis.PolynomialBox
import GNC.Analysis.PolynomialIntegral

/-! Certified polynomial observables of a validated ODE step. These estimates
apply to burn sensitivities as well as to the integrated state itself.
-/
namespace GNC.PolynomialODE
open Planning.PolynomialKernel PolynomialBounds PolynomialIntegral
variable {n : ℕ}

theorem Expr.value_continuous (e : Expr n) {x : ℝ → Fin n → ℝ} (hx : Continuous x) :
    Continuous (fun t => e.value (x t)) := by
  induction e with
  | constant c => exact continuous_const
  | var i => exact (continuous_apply i).comp hx
  | add a b ha hb => exact ha.add hb
  | multiply a b ha hb => exact ha.mul hb
  | negate a ha => exact ha.neg

theorem BoxStep.curve_box (s : BoxStep n) {f : Fin n → Expr n} (hs : s.Valid f)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) s.duration) (i : Fin n) :
    |curve s.coefficients t i| ≤ (s.region i:ℝ) := by
  obtain ⟨_,_,hb,_,_,hr,_⟩ := hs.2 i
  have hp := bound_sound (s.coefficients i) (show |t| ≤ (s.duration:ℝ) by
    rw [abs_of_nonneg ht.1]; exact ht.2)
  have hr' : (bound (s.coefficients i) s.duration:ℝ)+(s.error i:ℝ) ≤ (s.region i:ℝ) := by
    exact_mod_cast hr
  have hb' : (0:ℝ) < (s.error i:ℝ) := by exact_mod_cast hb
  change |evaluate ((s.coefficients i).map (Rat.castHom ℝ)) t| ≤ _
  linarith

theorem BoxStep.actual_box (s : BoxStep n) {f : Fin n → Expr n} (hs : s.Valid f)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) s.duration) (x : Fin n → ℝ)
    (hx : ∀ i, |x i-curve s.coefficients t i| ≤ (s.error i:ℝ)) (i : Fin n) :
    |x i| ≤ (s.region i:ℝ) := by
  obtain ⟨_,_,_,_,_,hr,_⟩ := hs.2 i
  have hp := bound_sound (s.coefficients i) (show |t| ≤ (s.duration:ℝ) by
    rw [abs_of_nonneg ht.1]; exact ht.2)
  have hr' : (bound (s.coefficients i) s.duration:ℝ)+(s.error i:ℝ) ≤ (s.region i:ℝ) := by
    exact_mod_cast hr
  have ha := abs_add_le (x i-curve s.coefficients t i) (curve s.coefficients t i)
  have he : x i-curve s.coefficients t i+curve s.coefficients t i = x i := by ring
  rw [he] at ha
  change |curve s.coefficients t i| ≤ (bound (s.coefficients i) s.duration:ℝ) at hp
  linarith [hx i]

theorem BoxStep.observable_error (s : BoxStep n) {f : Fin n → Expr n} (hs : s.Valid f)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) s.duration) (x : Fin n → ℝ)
    (hx : ∀ i, |x i-curve s.coefficients t i| ≤ (s.error i:ℝ)) (e : Expr n) :
    |e.value x-evaluate ((e.coefficients s.coefficients).map (Rat.castHom ℝ)) t| ≤
      (e.differenceMajorant s.region s.error:ℝ) := by
  rw [Expr.coefficients_correct]
  exact e.box_difference_bound (fun i => (hs.2 i).1) (fun i => (hs.2 i).2.2.1.le)
    x (curve s.coefficients t) (s.actual_box hs ht x hx) (s.curve_box hs ht) hx

theorem BoxStep.observable_integral (s : BoxStep n) {f : Fin n → Expr n} (hs : s.Valid f)
    (x : ℝ → Fin n → ℝ) (hx : Continuous x) (e : Expr n) {a b : ℚ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ s.duration)
    (herr : ∀ t ∈ Set.Icc (a:ℝ) (b:ℝ), ∀ i,
      |x t i-curve s.coefficients t i| ≤ (s.error i:ℝ)) :
    |(∫ t in (a:ℝ)..(b:ℝ), e.value (x t)) -
      ((integrate (e.coefficients s.coefficients) a b:ℚ):ℝ)| ≤
      ((b-a)*e.differenceMajorant s.region s.error:ℚ) := by
  rw [← rational_integral]
  have h := integral_error (fun t => e.value (x t))
    (evaluate ((e.coefficients s.coefficients).map (Rat.castHom ℝ)))
    (by exact_mod_cast hab)
    ((e.value_continuous hx).intervalIntegrable a b)
    ((evaluate_continuous _).intervalIntegrable a b)
    (fun t ht => s.observable_error hs
      ⟨le_trans (by exact_mod_cast ha) ht.1, le_trans ht.2 (by exact_mod_cast hb)⟩
      (x t) (herr t ht) e)
  simpa only [Rat.cast_mul, Rat.cast_sub] using h

theorem BoxStep.observable_integral_shifted (s : BoxStep n) {f : Fin n → Expr n} (hs : s.Valid f)
    (x : ℝ → Fin n → ℝ) (hx : Continuous x) (e : Expr n) (d : ℚ) {a b : ℚ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ s.duration)
    (herr : ∀ t ∈ Set.Icc (a:ℝ) (b:ℝ), ∀ i,
      |x ((d:ℝ)+t) i-curve s.coefficients t i| ≤ (s.error i:ℝ)) :
    |(∫ t in ((d+a:ℚ):ℝ)..((d+b:ℚ):ℝ), e.value (x t)) -
      ((integrate (e.coefficients s.coefficients) a b:ℚ):ℝ)| ≤
      ((b-a)*e.differenceMajorant s.region s.error:ℚ) := by
  have h := s.observable_integral hs (fun t => x ((d:ℝ)+t))
    (hx.comp (continuous_const.add continuous_id)) e ha hab hb herr
  rw [intervalIntegral.integral_comp_add_left (fun t => e.value (x t)) (d:ℝ)] at h
  simpa only [Rat.cast_add] using h

end GNC.PolynomialODE
