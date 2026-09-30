import GNC.Analysis.PolynomialObservable
import GNC.Analysis.PolynomialExtension

/-! Observable transfer for a scalar-radius polynomial step certificate.
The common state error may exceed a particular step's tighter error, so the
observable cube is enlarged by precisely that supplied error. -/
namespace GNC.PolynomialODE
open Planning.PolynomialKernel Set
variable {n : ℕ}

theorem Step.observable_error (s : Step n) {f : Fin n → Expr n} (hs : s.Valid f)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) s.duration) (x : Fin n → ℝ) {ε : ℚ}
    (hε : 0≤ε) (hx : ‖x-curve s.coefficients t‖≤(ε:ℝ)) (e : Expr n) :
    |e.value x-evaluate ((e.coefficients s.coefficients).map (Rat.castHom ℝ)) t|≤
      (e.slope (s.region+ε)*ε:ℚ) := by
  have hM : 0≤s.region := hs.2.1
  have he : (0:ℝ)≤ε := by exact_mod_cast hε
  have hy (i : Fin n) : |curve s.coefficients t i|≤(s.region:ℝ) := by
    have hp := PolynomialBounds.bound_sound (s.coefficients i)
      (show |t|≤(s.duration:ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2)
    have hb : (PolynomialBounds.bound (s.coefficients i) s.duration:ℝ)+s.error≤s.region :=
      by exact_mod_cast (hs.2.2.2.2.2.2.2 i).1
    have he0 : (0:ℝ)<s.error := by exact_mod_cast hs.2.2.2.2.1
    change |curve s.coefficients t i|≤_ at hp
    linarith
  have hd (i : Fin n) : |x i-curve s.coefficients t i|≤(ε:ℝ) := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using (norm_le_pi_norm _ i).trans hx
  have hxb (i : Fin n) : |x i|≤((s.region+ε:ℚ):ℝ) := by
    have h := abs_add_le (x i-curve s.coefficients t i) (curve s.coefficients t i)
    rw [sub_add_cancel] at h
    push_cast
    linarith [hy i,hd i]
  have hyb (i : Fin n) : |curve s.coefficients t i|≤((s.region+ε:ℚ):ℝ) := by
    push_cast
    linarith [hy i]
  rw [Expr.coefficients_correct,Rat.cast_mul]
  exact e.difference_bound (add_nonneg hM hε) x (curve s.coefficients t) he hxb hyb hd

end GNC.PolynomialODE
