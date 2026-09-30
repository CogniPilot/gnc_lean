import GNC.Magnus.FohDefectCertificate
import Mathlib.Analysis.SpecificLimits.Normed

/-! Actual-flow endpoint certificates for an arbitrary proposed exponent.
The exponent need not be polynomial in time, nor a truncation of Magnus.
In particular a cotangent-resummed exponent can be substituted directly.
The finite mismatch retains all cancellations before its norm is bounded.
-/
noncomputable section
open Finset Set
namespace GNC.Magnus
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A]

/-- Rational geometric majorant of the exponential tail. It is valid for
every radius strictly below `m+1`, including radii larger than one. -/
def fohExpTail (r : ℝ) (m : ℕ) : ℝ :=
  r ^ m * (m + 1) / ((Nat.factorial m : ℝ) * (m + 1 - r))

omit [NormOneClass A] in
/-- A posteriori certificate for any reported endpoint. The reported value can
be the exact real interpretation of floating-point output from any algorithm;
there is no assumption that it is an exponential or that the algorithm is exact.
The finite mismatch must be bounded against that reported value, not against an
idealized formula for its computation. -/
theorem foh_reported_endpoint_bound (a b reported : A) (Y : ℝ → A) (n : ℕ)
    {T : ℝ} (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t * (a + t • b)) t) :
    ‖Y T - reported‖ ≤ ‖fohTaylor a b n T - reported‖ +
      Real.exp ((‖a‖ + T * ‖b‖) * T) * (fohDefectRadius a b n T * T) := by
  have hf := fohTaylor_error_bound a b Y n hT hY0 hY
  have ht := norm_sub_le_norm_sub_add_norm_sub (Y T) (fohTaylor a b n T) reported
  linarith

omit [NormOneClass A] [CompleteSpace A] [NormedAlgebra ℝ A] in
/-- Compose a right-flow certificate using only the polynomial prefix and
step norms. Repeated application gives a piecewise-FOH endpoint bound. -/
theorem foh_right_product_error (X Y P Q : A) :
    ‖X * Y - P * Q‖ ≤
      (‖Q‖ + ‖Y - Q‖) * ‖X - P‖ + ‖Y - Q‖ * ‖P‖ := by
  have hid : X * Y - P * Q = (X - P) * Y + P * (Y - Q) := by noncomm_ring
  have hy : ‖Y‖ ≤ ‖Q‖ + ‖Y - Q‖ := by
    have h := norm_add_le Q (Y - Q)
    have he : Q + (Y - Q) = Y := by abel
    rw [he] at h
    exact h
  rw [hid]
  calc
    ‖(X - P) * Y + P * (Y - Q)‖ ≤ ‖X - P‖ * ‖Y‖ + ‖P‖ * ‖Y - Q‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖X - P‖ * (‖Q‖ + ‖Y - Q‖) + ‖P‖ * ‖Y - Q‖ := by gcongr
    _ = _ := by ring

/-- The sharper version retains the first omitted algebra power. -/
theorem foh_exp_tail_power (P : A) {r : ℝ} (hr : ‖P‖ ≤ r) (m : ℕ)
    (hm : r < m + 1) :
    ‖NormedSpace.exp P - ExponentialCertificate.polynomial P m‖ ≤
      ‖P ^ m‖ * (m + 1) / ((Nat.factorial m : ℝ) * (m + 1 - r)) := by
  have hr0 : 0 ≤ r := (norm_nonneg P).trans hr
  have hmp : (0 : ℝ) < m + 1 := by positivity
  have hq : ‖r / (m + 1)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr0 hmp.le)]
    exact (div_lt_one hmp).mpr hm
  have hs := (hasSum_geometric_of_norm_lt_one hq).mul_left (‖P ^ m‖ / (m.factorial : ℝ))
  have he := (hasSum_nat_add_iff' m).mpr
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) P)
  have hb : ‖NormedSpace.exp P - ExponentialCertificate.polynomial P m‖ ≤
      (‖P ^ m‖ / (m.factorial : ℝ)) * (1 - r / (m + 1))⁻¹ := by
    apply he.norm_le_of_bounded hs
    intro k
    have hf : (m.factorial : ℝ) * (m + 1) ^ k ≤ ((k + m).factorial : ℝ) := by
      exact_mod_cast (show m.factorial * (m + 1) ^ k ≤ (k + m).factorial by
        simpa only [Nat.add_comm] using (Nat.factorial_mul_pow_le_factorial (m := m) (n := k)))
    have hp : ‖P ^ (k + m)‖ ≤ ‖P ^ m‖ * r ^ k := by
      rw [Nat.add_comm k m, pow_add]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        ((norm_pow_le P k).trans (pow_le_pow_left₀ (norm_nonneg P) hr k)) (norm_nonneg _))
    calc
      ‖((Nat.factorial (k + m) : ℝ)⁻¹) • P ^ (k + m)‖ =
          ‖P ^ (k + m)‖ / ((k + m).factorial : ℝ) := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity)]
        ring
      _ ≤ (‖P ^ m‖ * r ^ k) / ((k + m).factorial : ℝ) :=
        div_le_div_of_nonneg_right hp (by positivity)
      _ ≤ (‖P ^ m‖ * r ^ k) / ((m.factorial : ℝ) * (m + 1) ^ k) :=
        div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (pow_nonneg hr0 _))
          (by positivity) hf
      _ = (‖P ^ m‖ / (m.factorial : ℝ)) * (r / (m + 1)) ^ k := by
        rw [div_pow]
        ring
  apply hb.trans_eq
  have hden : (m : ℝ) + 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  field_simp

/-- Norm-radius version of the geometric exponential tail. -/
theorem foh_exp_tail (P : A) {r : ℝ} (hr : ‖P‖ ≤ r) (m : ℕ)
    (hm : r < m + 1) :
    ‖NormedSpace.exp P - ExponentialCertificate.polynomial P m‖ ≤ fohExpTail r m := by
  apply (foh_exp_tail_power P hr m hm).trans
  unfold fohExpTail
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by positivity) (sub_nonneg.mpr hm.le))
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (norm_pow_le P m).trans (pow_le_pow_left₀ (norm_nonneg P) hr m)

/-- Arbitrary endpoint exponent, using the existing radius-at-most-one
tail. No property of the proposed exponent beyond its norm bound is assumed. -/
theorem foh_endpoint_certificate (a b P : A) (Y : ℝ → A) (n m : ℕ) {T r : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t * (a + t • b)) t)
    (hr : ‖P‖ ≤ r) (hr1 : r ≤ 1) (hm : 0 < m) :
    ‖Y T - NormedSpace.exp P‖ ≤
      ‖fohTaylor a b n T - ExponentialCertificate.polynomial P m‖ +
      Real.exp ((‖a‖ + T * ‖b‖) * T) * (fohDefectRadius a b n T * T) +
      r ^ m * (m + 1) / (Nat.factorial m * m) := by
  have hf := fohTaylor_error_bound a b Y n hT hY0 hY
  have he := ExponentialCertificate.remainder_bound P hr hr1 m hm
  have ht := norm_sub_le_norm_sub_add_norm_sub (Y T) (fohTaylor a b n T) (NormedSpace.exp P)
  have hp := norm_sub_le_norm_sub_add_norm_sub (fohTaylor a b n T)
    (ExponentialCertificate.polynomial P m) (NormedSpace.exp P)
  rw [norm_sub_rev (ExponentialCertificate.polynomial P m)] at hp
  linarith

/-- The full actual-flow certificate with a geometric tail for any radius
`r<m+1`. This applies directly to a cotangent-resummed endpoint exponent. -/
theorem foh_endpoint_certificate_geometric (a b P : A) (Y : ℝ → A) (n m : ℕ) {T r : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t * (a + t • b)) t)
    (hr : ‖P‖ ≤ r) (hm : r < m + 1) :
    ‖Y T - NormedSpace.exp P‖ ≤
      ‖fohTaylor a b n T - ExponentialCertificate.polynomial P m‖ +
      Real.exp ((‖a‖ + T * ‖b‖) * T) * (fohDefectRadius a b n T * T) + fohExpTail r m := by
  have hf := fohTaylor_error_bound a b Y n hT hY0 hY
  have he := foh_exp_tail P hr m hm
  have ht := norm_sub_le_norm_sub_add_norm_sub (Y T) (fohTaylor a b n T) (NormedSpace.exp P)
  have hp := norm_sub_le_norm_sub_add_norm_sub (fohTaylor a b n T)
    (ExponentialCertificate.polynomial P m) (NormedSpace.exp P)
  rw [norm_sub_rev (ExponentialCertificate.polynomial P m)] at hp
  linarith

/-- Scalar counterpart, allowing the Grönwall exponential itself to be
bounded by finite real arithmetic at an arbitrary nonnegative radius. -/
theorem foh_scalar_exp_bound {r : ℝ} (hr : 0 ≤ r) (m : ℕ) (hm : r < m + 1) :
    Real.exp r ≤ ExponentialCertificate.scalarPolynomial r m + fohExpTail r m := by
  have h := foh_exp_tail (A := ℝ) r (by simpa [Real.norm_eq_abs, abs_of_nonneg hr]) m hm
  have he : |Real.exp r - ExponentialCertificate.scalarPolynomial r m| ≤ fohExpTail r m := by
    simpa [ExponentialCertificate.polynomial, ExponentialCertificate.scalarPolynomial,
      Real.exp_eq_exp_ℝ, Real.norm_eq_abs, smul_eq_mul, div_eq_mul_inv, mul_comm] using h
  have hle := le_abs_self (Real.exp r - ExponentialCertificate.scalarPolynomial r m)
  linarith

/-- Fully finite arithmetic certificate with externally certified scalar
enclosures for the finite mismatch, ODE defect, and growth exponent.
This is suitable for a validated evaluator of nonpolynomial coefficients. -/
theorem foh_endpoint_certificate_finite (a b P : A) (Y : ℝ → A) (n m l : ℕ)
    {T r mismatch defect growth : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t * (a + t • b)) t)
    (hr : ‖P‖ ≤ r) (hm : r < m + 1)
    (hfinite : ‖fohTaylor a b n T - ExponentialCertificate.polynomial P m‖ ≤ mismatch)
    (hdefect : fohDefectRadius a b n T ≤ defect)
    (hgrowth : (‖a‖ + T * ‖b‖) * T ≤ growth) (hl : growth < l + 1) :
    ‖Y T - NormedSpace.exp P‖ ≤ mismatch +
      (ExponentialCertificate.scalarPolynomial growth l + fohExpTail growth l) * (defect * T) +
      fohExpTail r m := by
  have hg0 : 0 ≤ growth := (show 0 ≤ (‖a‖ + T * ‖b‖) * T by positivity).trans hgrowth
  have he : Real.exp ((‖a‖ + T * ‖b‖) * T) ≤
      ExponentialCertificate.scalarPolynomial growth l + fohExpTail growth l :=
    (Real.exp_le_exp.mpr hgrowth).trans (foh_scalar_exp_bound hg0 l hl)
  apply (foh_endpoint_certificate_geometric a b P Y n m hT hY0 hY hr hm).trans
  exact add_le_add (add_le_add hfinite
    (mul_le_mul he (mul_le_mul_of_nonneg_right hdefect hT)
      (mul_nonneg (fohDefectRadius_nonneg a b n hT) hT)
      ((Real.exp_pos _).le.trans he))) le_rfl

/-- A certified bound on an actual reported matrix is added separately;
the endpoint method certificate does not silently cover evaluator error. -/
theorem foh_endpoint_reported_certificate (a b P reported : A) (Y : ℝ → A)
    (n m l : ℕ) {T r mismatch defect growth evaluation : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t * (a + t • b)) t)
    (hr : ‖P‖ ≤ r) (hm : r < m + 1)
    (hfinite : ‖fohTaylor a b n T - ExponentialCertificate.polynomial P m‖ ≤ mismatch)
    (hdefect : fohDefectRadius a b n T ≤ defect)
    (hgrowth : (‖a‖ + T * ‖b‖) * T ≤ growth) (hl : growth < l + 1)
    (heval : ‖NormedSpace.exp P - reported‖ ≤ evaluation) :
    ‖Y T - reported‖ ≤ mismatch +
      (ExponentialCertificate.scalarPolynomial growth l + fohExpTail growth l) * (defect * T) +
      fohExpTail r m + evaluation := by
  exact (norm_sub_le_norm_sub_add_norm_sub (Y T) (NormedSpace.exp P) reported).trans
    (add_le_add (foh_endpoint_certificate_finite a b P Y n m l hT hY0 hY hr hm
      hfinite hdefect hgrowth hl) heval)

end GNC.Magnus
