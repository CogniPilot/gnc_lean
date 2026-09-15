import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact simplifications for quartics whose higher terms depend on the
squared transverse radius. These identities support the polynomial
comparator as well as geometric support certificates. -/
namespace GNC.RadialQuartic

def value (h₀ h₁ b₀₀ b₀₁ b₁₁ A g₀ g₁ u v : ℝ) : ℝ :=
  h₀*u+h₁*v+b₀₀*u^2+2*b₀₁*u*v+b₁₁*v^2+
    A*(u^2+v^2)^2+(g₀*u+g₁*v)*(u^2+v^2)

/-- A transverse quartic is quadratic on each fixed-radius circle. -/
theorem boundary_reduction (h₀ h₁ b₀₀ b₀₁ b₁₁ A g₀ g₁ u v r : ℝ)
    (hr : u^2+v^2=r) :
    value h₀ h₁ b₀₀ b₀₁ b₁₁ A g₀ g₁ u v=
      (h₀+r*g₀)*u+(h₁+r*g₁)*v+b₀₀*u^2+2*b₀₁*u*v+b₁₁*v^2+A*r^2 := by
  unfold value
  rw [hr]
  ring

/-- Positivity of a disk multiplier need not hold outside the disk. -/
theorem multiplier_identity (L A α g₀ g₁ r u v : ℝ) (hα : α≠0) :
    L+A*(u^2+v^2)+g₀*u+g₁*v=
      α*(u+g₀/(2*α))^2+α*(v+g₁/(2*α))^2+
        (L-(g₀^2+g₁^2)/(4*α)-(α-A)*r)+(α-A)*(r-u^2-v^2) := by
  field_simp
  ring

theorem multiplier_nonnegative (L A α g₀ g₁ r u v : ℝ)
    (hα : 0<α) (hA : A≤α) (hr : u^2+v^2≤r)
    (hk : 0≤L-(g₀^2+g₁^2)/(4*α)-(α-A)*r) :
    0≤L+A*(u^2+v^2)+g₀*u+g₁*v := by
  rw [multiplier_identity L A α g₀ g₁ r u v (ne_of_gt hα)]
  exact add_nonneg (add_nonneg
    (add_nonneg (mul_nonneg hα.le (sq_nonneg _)) (mul_nonneg hα.le (sq_nonneg _))) hk)
    (mul_nonneg (sub_nonneg.mpr hA) (by linarith))

/-- The free scalar t does not change the polynomial after lifting the
squared radius. It can be chosen to obtain a positive quadratic gap. -/
theorem radius_lift (h₀ h₁ b₀₀ b₀₁ b₁₁ A g₀ g₁ u v t : ℝ) :
    value h₀ h₁ b₀₀ b₀₁ b₁₁ A g₀ g₁ u v=
      h₀*u+h₁*v-2*t*(u^2+v^2)+(b₀₀+2*t)*u^2+2*b₀₁*u*v+(b₁₁+2*t)*v^2+
        A*(u^2+v^2)^2+g₀*u*(u^2+v^2)+g₁*v*(u^2+v^2) := by
  unfold value
  ring

end GNC.RadialQuartic
