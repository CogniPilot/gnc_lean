import GNC.Control.ThrustSupport

/-! A stronger conventional enclosure: bound axial and transverse pointing
components separately. This uses ordinary Euclidean vectors, and shares
the cap model's second-order axial loss without requiring Lie coordinates. -/
noncomputable section
open Matrix
namespace GNC.ThrustSupport

def cylinderBound (n h : Vec3) (κ tau : ℝ) : ℝ :=
  max (h ⬝ᵥ n) ((h ⬝ᵥ n)*κ)+tau*enorm (h-(h ⬝ᵥ n) • n)

theorem cap_transverse_bound (n q : Vec3) {κ tau : ℝ}
    (hn : n ⬝ᵥ n = 1) (hq : q ∈ Cap n κ)
    (hk : 0 ≤ κ) (ht : 0 ≤ tau) (hs : κ^2+tau^2 = 1) :
    enorm (q-(q ⬝ᵥ n) • n) ≤ tau := by
  have hsq := transverse_sq n q hn
  rw [unit_enorm q hq.1] at hsq
  have hc : κ ≤ q ⬝ᵥ n := by simpa only [dotProduct_comm] using hq.2
  nlinarith [sq_nonneg (q ⬝ᵥ n-κ), enorm_nonneg (q-(q ⬝ᵥ n) • n)]

/-- The cylinder is a genuine outer enclosure of the unit spherical cap. -/
theorem cylinder_support (n h q : Vec3) {κ tau : ℝ}
    (hn : n ⬝ᵥ n = 1) (hq : q ∈ Cap n κ)
    (hk : 0 ≤ κ) (ht : 0 ≤ tau) (hs : κ^2+tau^2 = 1) :
    h ⬝ᵥ q ≤ cylinderBound n h κ tau := by
  have hc : κ ≤ q ⬝ᵥ n := by simpa only [dotProduct_comm] using hq.2
  have hc1 : q ⬝ᵥ n ≤ 1 := by simpa [unit_enorm q hq.1, unit_enorm n hn] using dot_le_enorm q n
  have hpair : h ⬝ᵥ q = (h ⬝ᵥ n)*(q ⬝ᵥ n)+
      (h-(h ⬝ᵥ n) • n) ⬝ᵥ (q-(q ⬝ᵥ n) • n) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hn, dotProduct_comm n q]
    ring
  have htrans := (dot_le_enorm (h-(h ⬝ᵥ n) • n) (q-(q ⬝ᵥ n) • n)).trans
    (mul_le_mul_of_nonneg_left (cap_transverse_bound n q hn hq hk ht hs) (enorm_nonneg _))
  have ha : (h ⬝ᵥ n)*(q ⬝ᵥ n) ≤ max (h ⬝ᵥ n) ((h ⬝ᵥ n)*κ) := by
    by_cases hpos : 0 ≤ h ⬝ᵥ n
    · exact (by nlinarith : (h ⬝ᵥ n)*(q ⬝ᵥ n) ≤ h ⬝ᵥ n).trans (le_max_left _ _)
    · exact (by nlinarith : (h ⬝ᵥ n)*(q ⬝ᵥ n) ≤ (h ⬝ᵥ n)*κ).trans (le_max_right _ _)
  dsimp [cylinderBound]
  rw [hpair]
  nlinarith

/-- On nonpositive axial sensitivities, the cylinder agrees with the cap's
boundary certificate. Thus a first-order ball is not a strong baseline. -/
theorem cylinder_eq_boundary (n h : Vec3) {κ tau : ℝ}
    (hk : κ ≤ 1) (ha : h ⬝ᵥ n ≤ 0) :
    cylinderBound n h κ tau = (h ⬝ᵥ n)*κ+enorm (h-(h ⬝ᵥ n) • n)*tau := by
  rw [cylinderBound, max_eq_right (by nlinarith)]
  ring

/-- A first-order tangent-disk model with a quadratic remainder is also
valid. The explicit sine/cosine envelopes are hypotheses, not floating-point
trigonometric evaluations accepted as axioms. -/
theorem tangent_remainder_support (n h q : Vec3) {κ tau theta : ℝ}
    (hn : n ⬝ᵥ n = 1) (hq : q ∈ Cap n κ)
    (hk : 0 ≤ κ) (hk1 : κ ≤ 1) (ht : 0 ≤ tau) (hs : κ^2+tau^2 = 1)
    (hst : tau ≤ theta) (hct : 1-κ ≤ theta^2/2) :
    h ⬝ᵥ q ≤ h ⬝ᵥ n+theta*enorm (h-(h ⬝ᵥ n) • n)+theta^2/2*enorm h := by
  have hb := cylinder_support n h q hn hq hk ht hs
  have hn1 := unit_enorm n hn
  have ha : |h ⬝ᵥ n| ≤ enorm h := by
    apply abs_le.mpr
    constructor
    · have he := dot_le_enorm (-h) n
      simp only [neg_dotProduct, enorm_neg, hn1, mul_one] at he
      linarith
    · simpa [hn1] using dot_le_enorm h n
  have hax : max (h ⬝ᵥ n) ((h ⬝ᵥ n)*κ) ≤ h ⬝ᵥ n+theta^2/2*enorm h := by
    apply max_le
    · nlinarith [enorm_nonneg h, sq_nonneg theta]
    · have he := mul_le_mul_of_nonneg_left hct (enorm_nonneg h)
      have hf := mul_le_mul_of_nonneg_right (neg_le_abs (h ⬝ᵥ n)) (sub_nonneg.mpr hk1)
      have hg := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hk1)
      nlinarith
  have htr := mul_le_mul_of_nonneg_right hst (enorm_nonneg (h-(h ⬝ᵥ n) • n))
  dsimp [cylinderBound] at hb
  linarith

end GNC.ThrustSupport
