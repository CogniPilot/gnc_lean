import GNC.Control.DisturbedLogBackstepping
import GNC.Control.PointingLog
import GNC.Dynamics.VariableMassThrust
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Convert a proved attitude/rate storage envelope into physical thrust
support. The rotation axis is unrestricted. The quadratic cosine inequality
is global and proved in released mathlib; no numerical trigonometric
tolerance or small-angle equality is introduced.

The controller ODE, its chart and actuator realization still have to be
justified for a physical vehicle. These results compose its storage bound
with the actual rotation, rather than assuming a pointing envelope anew.
-/
noncomputable section
open Matrix Real Set
namespace GNC.LogBackstepping
open ThrustSupport

/-- A storage envelope directly certifies a spherical cap. Even when the
envelope is large the statement remains valid (and may become uninformative).
The cap threshold can be rational when the storage certificate is rational. -/
theorem rateStorage_cap (q z n : Vec3) {κ V : ℝ}
    (hκ : 0 < κ) (hn : n ⬝ᵥ n = 1) (hV : rateStorage κ q z ≤ V) :
    rotate (rotationExp q) n ∈ Cap n (1-V/κ) := by
  have hs : enorm q ^ 2 / 2 ≤ V/κ := by
    apply (le_div_iff₀ hκ).mpr
    have hz := lengthSq_nonneg z
    rw [enorm_sq]
    unfold rateStorage at hV
    nlinarith
  have hr := rotationExp_cap q n hn
  exact ⟨hr.1, (sub_le_sub_left hs 1).trans
    (one_sub_sq_div_two_le_cos.trans hr.2)⟩

/-- A left-invariant log error is in the reference body frame. Rotate both
physical directions by the reference attitude before interpreting the cap
in inertial coordinates; no fixed-reference-attitude assumption is needed. -/
theorem rateStorage_rotated_cap (R : SO3) (q z n : Vec3) {κ V : ℝ}
    (hκ : 0 < κ) (hn : n ⬝ᵥ n = 1) (hV : rateStorage κ q z ≤ V) :
    rotate (R*rotationExp q) n ∈ Cap (rotate R n) (1-V/κ) := by
  have h := rateStorage_cap q z n hκ hn hV
  simpa only [Cap, Set.mem_setOf_eq, rotate_mul, rotate_dot] using h

/-- The group's actual left-invariant error supplies the required attitude
factorization. A principal-log chart theorem can discharge herror. -/
theorem rateStorage_physical_cap (X Y : SE23) (ξ : LogState) (z n : Vec3) {κ V : ℝ}
    (herror : groupExp ξ = SE23.error Y X) (hκ : 0 < κ)
    (hn : n ⬝ᵥ n = 1) (hV : rateStorage κ (ξ 2) z ≤ V) :
    rotate X.rot n ∈ Cap (rotate Y.rot n) (1-V/κ) := by
  have hr : rotationExp (ξ 2) = Y.rot⁻¹*X.rot := congrArg SE23.rot herror
  have he : Y.rot*rotationExp (ξ 2) = X.rot := by rw [hr]; simp
  simpa only [he] using rateStorage_rotated_cap Y.rot (ξ 2) z n hκ hn hV

/-- Fixed thrust magnitude produces a one-sided axial loss, quadratic in
the certified log-angle radius. Known variable mass enters through a=F/m. -/
theorem rateStorage_axial (q z n : Vec3) {κ V a : ℝ}
    (hκ : 0 < κ) (hn : n ⬝ᵥ n = 1) (hV : rateStorage κ q z ≤ V)
    (ha : 0 ≤ a) :
    -a*(V/κ) ≤ n ⬝ᵥ (a • (rotate (rotationExp q) n-n)) ∧
      n ⬝ᵥ (a • (rotate (rotationExp q) n-n)) ≤ 0 := by
  simpa only [sub_sub_cancel] using
    axial_acceleration_bounds n _ hn (rateStorage_cap q z n hκ hn hV) ha

/-- Directional support with joint magnitude and pointing uncertainty.
The same storage envelope feeds every direction, and magnitude and pointing
need not be independent. A square-length inequality can certify s exactly. -/
theorem rateStorage_thrust_support (q z n h : Vec3) {κ V a a₀ δ ell s : ℝ}
    (hκ : 0 < κ) (hn : n ⬝ᵥ n = 1) (hV : rateStorage κ q z ≤ V)
    (ha₀ : 0 ≤ a₀) (hδ : |a-a₀| ≤ δ) (hell : 0 ≤ ell) (hs : 0 ≤ s)
    (hlength : lengthSq (h+ell • n) ≤ s^2) :
    h ⬝ᵥ (a • rotate (rotationExp q) n-a₀ • n) ≤
      a₀*(s-ell*(1-V/κ)-h ⬝ᵥ n)+δ*enorm h := by
  let r := rotate (rotationExp q) n
  have hcap := rateStorage_cap q z n hκ hn hV
  have hp := cap_support_of_squared_bound n h r (1-V/κ) ell s hcap hell hs hlength
  have hm := dot_le_enorm h ((a-a₀) • r)
  rw [enorm_smul, unit_enorm r hcap.1, mul_one] at hm
  have hb := mul_le_mul_of_nonneg_left hδ (enorm_nonneg h)
  rw [thrust_error_split, dotProduct_add, dotProduct_smul, smul_eq_mul,
    dotProduct_sub]
  have he := mul_le_mul_of_nonneg_left (sub_le_sub_right hp (h ⬝ᵥ n)) ha₀
  dsimp [r] at hm
  nlinarith

/-- The inertial directional query is pulled into the reference body frame.
The reference attitude is evaluated at this time, before integration. -/
theorem rateStorage_rotated_thrust_support (R : SO3) (q z n h : Vec3)
    {κ V a a₀ δ ell s : ℝ}
    (hκ : 0 < κ) (hn : n ⬝ᵥ n = 1) (hV : rateStorage κ q z ≤ V)
    (ha₀ : 0 ≤ a₀) (hδ : |a-a₀| ≤ δ) (hell : 0 ≤ ell) (hs : 0 ≤ s)
    (hlength : lengthSq (rotate R⁻¹ h+ell • n) ≤ s^2) :
    h ⬝ᵥ rotate R (a • rotate (rotationExp q) n-a₀ • n) ≤
      a₀*(s-ell*(1-V/κ)-rotate R⁻¹ h ⬝ᵥ n)+δ*enorm h := by
  rw [rotate_dot_pull]
  simpa only [rotate_enorm] using
    rateStorage_thrust_support q z n (rotate R⁻¹ h) hκ hn hV ha₀ hδ hell hs hlength

/-- Force and mass errors retain their declared joint envelope. This is the
input support to use in the finite-horizon adjoint theorem, with its actual
reference-dependent direction h(t); it is not itself an arrival certificate. -/
theorem rateStorage_force_mass_support (q z n h : Vec3)
    {κ V F F₀ m m₀ reserve forceError massError ell s : ℝ}
    (hκ : 0 < κ) (hn : n ⬝ᵥ n = 1) (hV : rateStorage κ q z ≤ V)
    (hr : 0 < reserve) (hm : reserve ≤ m) (hm₀ : reserve ≤ m₀)
    (hF : |F-F₀| ≤ forceError) (hM : |m-m₀| ≤ massError)
    (ha₀ : 0 ≤ F₀/m₀) (hell : 0 ≤ ell) (hs : 0 ≤ s)
    (hlength : lengthSq (h+ell • n) ≤ s^2) :
    h ⬝ᵥ ((F/m) • rotate (rotationExp q) n-(F₀/m₀) • n) ≤
      (F₀/m₀)*(s-ell*(1-V/κ)-h ⬝ᵥ n)+
        (forceError/reserve+|F₀| *massError/reserve^2)*enorm h :=
  rateStorage_thrust_support q z n h hκ hn hV ha₀
    (VariableMassThrust.force_mass_error_bound hr hm hm₀ hF hM) hell hs hlength

end GNC.LogBackstepping
