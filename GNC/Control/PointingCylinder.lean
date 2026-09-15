import GNC.Control.PointingEnclosure

/-! Rational outer cylinders for physical unit pointing caps. The transverse
radius can be rounded outward; equality with the exact cap radius is not
required. The same physical set is available in Cartesian or Lie coordinates.
-/
noncomputable section
namespace GNC.ThrustSupport
open Matrix

theorem transverse_pair_bound {a b x z B T : ℝ}
    (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hr : a^2+b^2 ≤ B^2) (hw : x^2+z^2 ≤ T^2) :
    |a*x+b*z| ≤ B*T := by
  have hp := mul_le_mul hr hw (by positivity : 0 ≤ x^2+z^2) (sq_nonneg B)
  have he : (a*x+b*z)^2+(a*z-b*x)^2 = (a^2+b^2)*(x^2+z^2) := by ring
  apply abs_le_of_sq_le_sq _ (mul_nonneg hB hT)
  nlinarith [sq_nonneg (a*z-b*x)]

/-- Cap about the second coordinate. eta is its maximum axial loss; tau
is any certified transverse radius, so rational outward rounding is explicit.
-/
theorem cap_coordinate_cylinder (q : Vec3) {eta tau : ℝ}
    (hq : q ∈ Cap ![0,1,0] (1-eta))
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (ht : 0 ≤ tau)
    (hs : 2*eta-eta^2 ≤ tau^2) :
    q 0^2+q 2^2 ≤ tau^2 ∧ |q 1-1| ≤ eta := by
  have hu : q 0^2+q 1^2+q 2^2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using hq.1
  have hl : 1-eta ≤ q 1 := by
    simpa [dotProduct, Fin.sum_univ_succ] using hq.2
  have hp : 0 ≤ q 1 := by linarith
  have h1 : q 1 ≤ 1 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 2)]
  refine ⟨?_, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  nlinarith [sq_nonneg (q 1-(1-eta))]

/-- Magnitude may vary throughout a burn. The bound does not assume
independence between the magnitude and pointing histories. -/
theorem scaled_coordinate_cylinder (q : Vec3) {eta tau a B : ℝ}
    (hq : q ∈ Cap ![0,1,0] (1-eta))
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (ht : 0 ≤ tau)
    (hs : 2*eta-eta^2 ≤ tau^2) (ha : 0 ≤ a) (haB : a ≤ B) :
    (a*q 0)^2+(a*q 2)^2 ≤ (B*tau)^2 ∧ |a*(q 1-1)| ≤ B*eta := by
  have hc := cap_coordinate_cylinder q hq he he1 ht hs
  have hB := ha.trans haB
  constructor
  · have hm := mul_le_mul_of_nonneg_left hc.1 (sq_nonneg a)
    have hab : a*tau ≤ B*tau := mul_le_mul_of_nonneg_right haB ht
    nlinarith [sq_nonneg (B*tau-a*tau), mul_nonneg ha ht]
  · rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left hc.2 ha).trans
      (mul_le_mul_of_nonneg_right haB he)

end GNC.ThrustSupport
