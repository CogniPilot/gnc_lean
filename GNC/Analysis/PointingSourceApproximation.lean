import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Scalar pointing-source approximations. The input `s` is the squared
transverse radius, so a quadratic profile in `s` is quartic in `(u,v)`.
These identities explain the constrained comparator's proposal; they do
not assert optimality of its numerical coefficient or root finder. -/
namespace GNC.PointingSourceApproximation
noncomputable section

def depth (s : ℝ) : ℝ := 1-Real.sqrt (1-s)
def quotient (s : ℝ) : ℝ := 1/(2*(1+Real.sqrt (1-s))^2)
def profile (b s : ℝ) : ℝ := s/2+b*s^2
def quotientSlope (s : ℝ) : ℝ :=
  1/(2*Real.sqrt (1-s)*(1+Real.sqrt (1-s))^3)

theorem depth_zero : depth 0=0 := by norm_num [depth]
theorem profile_zero (b : ℝ) : profile b 0=0 := by simp [profile]

theorem profile_tangent (b : ℝ) : HasDerivAt (profile b) (1/2) 0 := by
  convert ((hasDerivAt_id (0:ℝ)).div_const 2).add
    (((hasDerivAt_id (0:ℝ)).pow 2).const_mul b) using 1 <;> norm_num [profile]

theorem depth_tangent : HasDerivAt depth (1/2) 0 := by
  have h := ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id 0)).sqrt
    (by norm_num : (1:ℝ)-0≠0)
  convert (hasDerivAt_const (0:ℝ) (1:ℝ)).sub h using 1 <;> norm_num [depth]

theorem remainder_identity (b s : ℝ) (hs : s≤1) :
    depth s-profile b s=s^2*(quotient s-b) := by
  set z := Real.sqrt (1-s) with hz
  have hz0 : 0≤z := Real.sqrt_nonneg _
  have hz2 : z^2=1-s := Real.sq_sqrt (by linarith)
  have he : s=1-z^2 := by linarith
  have hn : 1+z≠0 := by positivity
  change 1-z-(s/2+b*s^2)=s^2*(1/(2*(1+z)^2)-b)
  rw [he]
  field_simp
  <;> ring

theorem quotient_derivative (s : ℝ) (hs : s<1) :
    HasDerivAt quotient (quotientSlope s) s := by
  have hz : Real.sqrt (1-s)≠0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have ha : 1+Real.sqrt (1-s)≠0 := by positivity
  have h := ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).sqrt
    (by linarith : (1:ℝ)-s≠0)
  convert (hasDerivAt_const s (1:ℝ)).div
    ((((hasDerivAt_const s (1:ℝ)).add h).pow 2).const_mul 2)
    (by dsimp; positivity) using 1
  dsimp [quotientSlope]
  field_simp
  <;> ring

theorem weighted_remainder_derivative (b s : ℝ) (hs : s<1) :
    HasDerivAt (fun x => x^2*(quotient x-b))
      (2*s*(quotient s-b)+s^2*quotientSlope s) s := by
  convert ((hasDerivAt_id s).pow 2).mul
    ((quotient_derivative s hs).sub_const b) using 1 <;> dsimp <;> ring

theorem remainder_derivative (b s : ℝ) (hs : s<1) :
    HasDerivAt (fun x => depth x-profile b x)
      (2*s*(quotient s-b)+s^2*quotientSlope s) s := by
  apply (weighted_remainder_derivative b s hs).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hs] with x hx
  exact remainder_identity b x hx.le

theorem stationary_coefficient (s q d b : ℝ) (hs : s≠0) :
    (2*s*(q-b)+s^2*d=0) ↔ b=q+s*d/2 := by
  constructor
  · intro h
    have he : (2*s)*(q+s*d/2-b)=0 := by linear_combination h
    have hz := (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hs)
    linarith
  · intro h
    rw [h]
    ring

theorem equioscillation_equation (h s q qh d : ℝ) :
    s^2*(q-(q+s*d/2))+h^2*(qh-(q+s*d/2))=
      h^2*(qh-q)-(s^2+h^2)*s*d/2 := by ring

end
end GNC.PointingSourceApproximation
