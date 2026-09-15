import GNC.Dynamics.OrbitalReference

/-! Concrete, sampling-free envelopes for the paper's two reference missions.
Units are the same normalized gravitational units as `fuel_study.reference`.
These are bounds on existing exact trajectories, not a certificate for a
numerical interpolant, transition kernel, or complete chaser mission.
-/
noncomputable section
open Set Real GNC
open scoped RealInnerProductSpace
namespace GNC.Applications.OrbitalFuel.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def earthLength : ℝ := 6728137
def earthMu : ℝ := 398600441800000
def earthH : ℝ := 50000/earthLength
def earthCoefficient : ℝ := (11/200000000000000)*earthLength
def earthThrust : ℝ := (1/200000)*earthLength^2/earthMu

def earthForce (p v wind direction : E) : E :=
  OrbitalReference.noncentral earthCoefficient earthH (999/1000) earthThrust p v wind direction

/-- The density ratio never exceeds 1.015 inside the proposed annulus.
Mathlib's exponential remainder is used; no numerical exponential is trusted. -/
theorem earth_density_bound (p : E) (hr : 9989/10000 ≤ ‖p‖) :
    Atmosphere.density earthH (999/1000) p ≤ 203/200 := by
  have hx : -(‖p‖-999/1000)/earthH ≤ 7/500 := by
    dsimp [earthH, earthLength]
    linarith
  have hb := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
    (show |(7/500:ℝ)| ≤ 1 by norm_num))).2
  have he : Real.exp (7/500:ℝ) ≤ 203/200 := by linarith
  exact (Real.exp_le_exp.mpr hx).trans he

theorem earth_force_bound (p v wind direction : E)
    (hr : 9989/10000 ≤ ‖p‖) (hR : ‖p‖ ≤ 10011/10000) (hV : ‖v‖ ≤ 501/500)
    (hwind : ‖wind‖ ≤ (8/125)*‖p‖) (hu : ‖direction‖ ≤ 1) :
    ‖earthForce p v wind direction‖ ≤ 1/1000000 := by
  have hc0 : 0 ≤ earthCoefficient := by norm_num [earthCoefficient, earthLength]
  have hrho : 0 ≤ Atmosphere.density earthH (999/1000) p := (Real.exp_pos _).le
  have hc : |earthCoefficient*Atmosphere.density earthH (999/1000) p| ≤
      earthCoefficient*(203/200) := by
    rw [abs_of_nonneg (mul_nonneg hc0 hrho)]
    exact mul_le_mul_of_nonneg_left (earth_density_bound p hr) hc0
  have hw := OrbitalReference.relative_wind_bound p v wind
    (show (0:ℝ) ≤ 8/125 by norm_num) hR hV hwind
  have h := OrbitalReference.noncentral_bound earthCoefficient earthH (999/1000) earthThrust
    p v wind direction hc hw hu
  exact h.trans (by norm_num [earthCoefficient, earthLength, earthThrust, earthMu])

/-- Exact Earth-reference radius and speed envelope for all t in [0,4]. -/
theorem earth_annulus (p v wind direction : ℝ → E)
    (hpcont : Continuous p) (hvcont : Continuous v)
    (hp : ∀ t ∈ Icc (0:ℝ) 4, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Icc (0:ℝ) 4, HasDerivAt v
      (Gravity.field 1 (p t)+earthForce (p t) (v t) (wind t) (direction t)) t)
    (hwind : ∀ t ∈ Icc (0:ℝ) 4, ‖wind t‖ ≤ (8/125)*‖p t‖)
    (hu : ∀ t ∈ Icc (0:ℝ) 4, ‖direction t‖ ≤ 1)
    (hr : ‖p 0‖ = 999/1000) (hs : ‖v 0‖^2 = 1001/999) (ho : ⟪p 0,v 0⟫ = 0) :
    ∀ t ∈ Icc (0:ℝ) 4,
      9989/10000 < ‖p t‖ ∧ ‖p t‖ < 10011/10000 ∧ ‖v t‖ < 501/500 := by
  have hi := OrbitalReference.periapsis_invariants (p 0) (v 0)
    (show (0:ℝ) ≤ 1/1000 by norm_num) (show (1/1000:ℝ) < 1 by norm_num)
    (by norm_num; exact hr) (by norm_num; exact hs) ho
  apply OrbitalReference.annulus p v
    (fun t => earthForce (p t) (v t) (wind t) (direction t))
    (mu := 1) (T := 4) (D := 1/1000000)
    (energy := -1/2+(501/500)*(1/1000000)*4)
    (hminus := 1-(1/1000)^2-4*(10011/10000)^2*(501/500)*(1/1000000)*4)
    (hplus := 1-(1/1000)^2+4*(10011/10000)^2*(501/500)*(1/1000000)*4)
    (ecc := 1/1000+4*(10011/10000)*(501/500)*(1/1000000)*4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hpcont hvcont hp hv
  · intro t ht hlo hhi hvel
    exact earth_force_bound (p t) (v t) (wind t) (direction t) hlo hhi hvel (hwind t ht) (hu t ht)
  · refine ⟨by rw [hr]; norm_num, by rw [hr]; norm_num, ?_⟩
    nlinarith [norm_nonneg (v 0)]
  · rw [hi.1]
  · rw [hi.2.1]
  · rw [hi.2.1]
  · rw [hi.2.2]
  all_goals norm_num

/-- Solar thrust normalization uses exact physical parameters. -/
def solarLength : ℝ := 149597870700
def solarMu : ℝ := 132712440018000000000
def solarThrust : ℝ := (1/5000000)*solarLength^2/solarMu

theorem solar_thrust_bound (direction : E) (hu : ‖direction‖ ≤ 1) :
    ‖solarThrust • direction‖ ≤ 17/500000 := by
  rw [norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left hu (abs_nonneg solarThrust)
  exact h.trans (by norm_num [solarThrust, solarLength, solarMu])

theorem solar_annulus (p v direction : ℝ → E)
    (hpcont : Continuous p) (hvcont : Continuous v)
    (hp : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt v
      (Gravity.field 1 (p t)+solarThrust • direction t) t)
    (hu : ∀ t ∈ Icc (0:ℝ) (3/5), ‖direction t‖ ≤ 1)
    (hr : ‖p 0‖ = 4/5) (hs : ‖v 0‖^2 = 3/2) (ho : ⟪p 0,v 0⟫ = 0) :
    ∀ t ∈ Icc (0:ℝ) (3/5),
      7997/10000 < ‖p t‖ ∧ ‖p t‖ < 2401/2000 ∧ ‖v t‖ < 613/500 := by
  have hi := OrbitalReference.periapsis_invariants (p 0) (v 0)
    (show (0:ℝ) ≤ 1/5 by norm_num) (show (1/5:ℝ) < 1 by norm_num)
    (by norm_num; exact hr) (by norm_num; exact hs) ho
  apply OrbitalReference.annulus p v (fun t => solarThrust • direction t)
    (mu := 1) (T := 3/5) (D := 17/500000)
    (energy := -1/2+(613/500)*(17/500000)*(3/5))
    (hminus := 1-(1/5)^2-4*(2401/2000)^2*(613/500)*(17/500000)*(3/5))
    (hplus := 1-(1/5)^2+4*(2401/2000)^2*(613/500)*(17/500000)*(3/5))
    (ecc := 1/5+4*(2401/2000)*(613/500)*(17/500000)*(3/5))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hpcont hvcont hp hv
  · intro t ht _ _ _
    exact solar_thrust_bound (direction t) (hu t ht)
  · refine ⟨by rw [hr]; norm_num, by rw [hr]; norm_num, ?_⟩
    nlinarith [norm_nonneg (v 0)]
  · rw [hi.1]
  · rw [hi.2.1]
  · rw [hi.2.1]
  · rw [hi.2.2]
  all_goals norm_num


/-- Rational upper bounds for conversion back to SI units and Earth spin. -/
theorem earth_units :
    Real.sqrt (earthMu/earthLength) ≤ 7697 ∧
    (1458423/20000000000)*Real.sqrt (earthLength^3/earthMu) ≤ 8/125 := by
  have h₁ := Real.sq_sqrt (show (0:ℝ) ≤ earthMu/earthLength by norm_num [earthMu, earthLength])
  have h₂ := Real.sq_sqrt (show (0:ℝ) ≤ earthLength^3/earthMu by norm_num [earthMu, earthLength])
  norm_num [earthMu, earthLength] at h₁ h₂ ⊢
  constructor <;> nlinarith [Real.sqrt_nonneg (earthMu/earthLength),
    Real.sqrt_nonneg (earthLength^3/earthMu)]

theorem solar_units : Real.sqrt (solarMu/solarLength) ≤ 29785 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ solarMu/solarLength by norm_num [solarMu, solarLength])
  norm_num [solarMu, solarLength] at h ⊢
  nlinarith

end GNC.Applications.OrbitalFuel.Reference
