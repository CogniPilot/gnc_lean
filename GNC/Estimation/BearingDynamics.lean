import GNC.Estimation.BearingComparison
import GNC.Control.LogBackstepping

/-! Quantifying the remaining symmetry benefit in the paper's bearing model.

Embedded propagation is already exactly linear and preserves error length.
Rotational and projected tangent corrections coincide for the same scalar
gain. Their actual unit-bearing trajectories obey the same nonlinear scalar
energy equation. This does not identify an arbitrary embedded EKF (including
its constraint pseudomeasurement and Riccati equation) with an EqF.
-/
noncomputable section
open Matrix Real Set
namespace GNC.BearingDynamics

def drift (ω q : Vec3) : Vec3 := -(ω ⨯₃ q)
def tangentCorrection (k : ℝ) (q y : Vec3) : Vec3 :=
  k • (y-(q ⬝ᵥ y) • q)
def rotationalCorrection (k : ℝ) (q y : Vec3) : Vec3 :=
  (k • (q ⨯₃ (y-q))) ⨯₃ q
def energy (q y : Vec3) : ℝ := 1-q ⬝ᵥ y

theorem dot_derivative {q y : ℝ → Vec3} {dq dy : Vec3} {t : ℝ}
    (hq : HasDerivAt q dq t) (hy : HasDerivAt y dy t) :
    HasDerivAt (fun s => q s ⬝ᵥ y s) (dq ⬝ᵥ y t+q t ⬝ᵥ dy) t := by
  have h i := (hasDerivAt_pi.mp hq i).mul (hasDerivAt_pi.mp hy i)
  convert ((h 0).add (h 1)).add (h 2) using 1
  · ext s; simp [dotProduct, Fin.sum_univ_succ]; ring
  · simp [dotProduct, Fin.sum_univ_succ]; ring

/-- The embedded EKF's propagation Taylor remainder is identically zero. -/
theorem drift_exact (ω q y : Vec3) : drift ω y-drift ω q = drift ω (y-q) := by
  ext i
  fin_cases i <;> simp [drift, crossProduct] <;> ring

theorem drift_error_derivative {q y : ℝ → Vec3} {ω : Vec3} {t : ℝ}
    (hq : HasDerivAt q (drift ω (q t)) t)
    (hy : HasDerivAt y (drift ω (y t)) t) :
    HasDerivAt (fun s => y s-q s) (drift ω (y t-q t)) t := by
  simpa only [drift_exact] using hy.sub hq

/-- Exact physical error growth factor one during common noiseless
rotation. This is true in the embedded EKF coordinates as well as EqF's. -/
theorem propagation_distance_constant (ω q y : ℝ → Vec3)
    (hq : ∀ t, HasDerivAt q (drift (ω t) (q t)) t)
    (hy : ∀ t, HasDerivAt y (drift (ω t) (y t)) t) (a t : ℝ) :
    enorm (y t-q t) = enorm (y a-q a) := by
  have h := attitude_lengthSq_constant ω (fun s => y s-q s)
    (fun s i => hasDerivAt_pi.mp (drift_error_derivative (hq s) (hy s)) i) t a
  rw [← enorm_sq, ← enorm_sq] at h
  nlinarith [enorm_nonneg (y t-q t), enorm_nonneg (y a-q a)]

/-- With identical scalar gain, the rotational correction and the
projected tangent EKF correction are the same physical vector field. -/
theorem corrections_equal (k : ℝ) (q y : Vec3) (hq : q ⬝ᵥ q = 1) :
    rotationalCorrection k q y = tangentCorrection k q y := by
  have he : (q ⨯₃ (y-q)) ⨯₃ q = y-(q ⬝ᵥ y) • q := by
    rw [map_sub, cross_self, sub_zero, cross_cross_eq_smul_sub_smul, hq, one_smul]
    rw [dotProduct_comm y q]
  change (crossProduct (k • (q ⨯₃ (y-q)))) q = _
  rw [map_smul]
  simp only [LinearMap.smul_apply, he, tangentCorrection]

theorem correction_tangent (k : ℝ) (q y : Vec3) (hq : q ⬝ᵥ q = 1) :
    q ⬝ᵥ tangentCorrection k q y = 0 := by
  simp [tangentCorrection, dotProduct_sub, dotProduct_smul, hq]

/-- Continuous Kalman--Bucy correction with tangent isotropic covariance
p(I-qq^T), the normalized measurement Jacobian, and measurement weight nI.
The same scalar gain p/n gives the rotational correction above. -/
theorem tangent_kalman_correction (p n : ℝ) (q y : Vec3) (hq : q ⬝ᵥ q = 1) :
    (p/n) • BearingComparison.unitJacobian q
      (BearingComparison.unitJacobian q (y-q)) = tangentCorrection (p/n) q y := by
  simp only [BearingComparison.unitJacobian, dotProduct_sub, dotProduct_smul,
    hq, smul_eq_mul, mul_one, tangentCorrection]
  module

theorem dot_young (x y : Vec3) {k : ℝ} (hk : 0 < k) :
    x ⬝ᵥ y ≤ (k/2)*enorm x^2+enorm y^2/(2*k) := by
  have h := Lyapunov.inner_young (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))
    (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 3)) hk
  change y ⬝ᵥ star x ≤ (k/2)*enorm x^2+(1/(2*k))*enorm y^2 at h
  simp only [star_trivial, dotProduct_comm y x] at h
  convert h using 1
  ring

/-- Tangent perturbations collect gyro mismatch and measurement forcing.
This exact scalar derivative is the starting point for a common noise bound. -/
theorem perturbed_energy_derivative {q y : ℝ → Vec3} {ω d : Vec3} {k t : ℝ}
    (hq : HasDerivAt q (drift ω (q t)+tangentCorrection k (q t) (y t)+d) t)
    (hy : HasDerivAt y (drift ω (y t)) t) (hu : y t ⬝ᵥ y t = 1) :
    HasDerivAt (fun s => energy (q s) (y s))
      (-k*(2-energy (q t) (y t))*energy (q t) (y t)-d ⬝ᵥ y t) t := by
  convert (dot_derivative hq hy).const_sub 1 using 1
  have hc : (ω ⨯₃ q t) ⬝ᵥ y t+q t ⬝ᵥ (ω ⨯₃ y t) = 0 := by
    simp [crossProduct, dotProduct, Fin.sum_univ_succ]
    ring
  simp only [drift, tangentCorrection, energy, add_dotProduct, neg_dotProduct,
    dotProduct_neg, smul_dotProduct, sub_dotProduct, hu, smul_eq_mul]
  nlinarith

theorem energy_nonneg (q y : Vec3) (hq : q ⬝ᵥ q = 1) (hy : y ⬝ᵥ y = 1) :
    0 ≤ energy q y := by
  have h := lengthSq_nonneg (y-q)
  simp only [← dot_self_lengthSq, sub_dotProduct, dotProduct_sub, hq, hy,
    dotProduct_comm y q] at h
  dsimp [energy]
  linarith

theorem energy_chord (q y : Vec3) (hq : q ⬝ᵥ q = 1) (hy : y ⬝ᵥ y = 1) :
    enorm (y-q)^2 = 2*energy q y := by
  simp only [enorm_sq, ← dot_self_lengthSq, sub_dotProduct, dotProduct_sub,
    hq, hy, dotProduct_comm y q, energy]
  ring

/-- Exact closed-loop energy equation, derived from the physical vector
fields; the common angular velocity cancels for every magnitude. -/
theorem energy_derivative {q y : ℝ → Vec3} {ω : Vec3} {k t : ℝ}
    (hq : HasDerivAt q (drift ω (q t)+tangentCorrection k (q t) (y t)) t)
    (hy : HasDerivAt y (drift ω (y t)) t)
    (hu : y t ⬝ᵥ y t = 1) :
    HasDerivAt (fun s => energy (q s) (y s))
      (-k*(2-energy (q t) (y t))*energy (q t) (y t)) t := by
  convert (dot_derivative hq hy).const_sub 1 using 1
  have hc : (ω ⨯₃ q t) ⬝ᵥ y t+q t ⬝ᵥ (ω ⨯₃ y t) = 0 := by
    simp [crossProduct, dotProduct, Fin.sum_univ_succ]
    ring
  simp only [drift, tangentCorrection, energy, add_dotProduct, neg_dotProduct,
    dotProduct_neg, smul_dotProduct, sub_dotProduct, hu, smul_eq_mul]
  nlinarith

/-- Any chosen cap V<=rho<2 is invariant for positive gain. The antipodal
equilibrium at V=2 is excluded explicitly; it cannot be certified away. -/
theorem energy_cap {V k : ℝ → ℝ} {k₀ ρ a b : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ < 2) (hk₀ : 0 < k₀)
    (hk : ∀ t ∈ Ico a b, k₀ ≤ k t)
    (hd : ∀ t ∈ Icc a b, HasDerivAt V (-k t*(2-V t)*V t) t)
    (hinit : V a ≤ ρ) : ∀ t ∈ Icc a b, V t ≤ ρ := by
  apply image_le_of_deriv_right_lt_deriv_boundary
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    hinit (fun t => hasDerivAt_const t ρ)
  intro t ht he
  rw [he]
  have hkt : 0 < k t := lt_of_lt_of_le hk₀ (hk t ht)
  nlinarith [mul_pos (mul_pos hkt (sub_pos.mpr hρ2)) hρ]

/-- A quantitative convergence theorem shared by the matched rotational
and tangent observers. No angular-rate magnitude enters its rate. -/
theorem observer_convergence (ω q y : ℝ → Vec3) (k : ℝ → ℝ) {k₀ ρ a b : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ < 2) (hk₀ : 0 < k₀)
    (hk : ∀ t ∈ Ico a b, k₀ ≤ k t)
    (hq : ∀ t ∈ Icc a b,
      HasDerivAt q (drift (ω t) (q t)+tangentCorrection (k t) (q t) (y t)) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (drift (ω t) (y t)) t)
    (hqu : ∀ t ∈ Icc a b, q t ⬝ᵥ q t = 1)
    (hyu : ∀ t ∈ Icc a b, y t ⬝ᵥ y t = 1)
    (hinit : energy (q a) (y a) ≤ ρ) :
    ∀ t ∈ Icc a b, energy (q t) (y t) ≤ ρ ∧
      energy (q t) (y t) ≤ energy (q a) (y a)*exp (-k₀*(2-ρ)*(t-a)) := by
  have hd := fun t ht => energy_derivative (hq t ht) (hy t ht) (hyu t ht)
  have hcap := energy_cap hρ hρ2 hk₀ hk hd hinit
  have he := Lyapunov.exponential_bound_on (c := k₀*(2-ρ)) hd (by
    intro t ht
    have hv := energy_nonneg (q t) (y t) (hqu t ⟨ht.1,ht.2.le⟩) (hyu t ⟨ht.1,ht.2.le⟩)
    have hc := hcap t ⟨ht.1,ht.2.le⟩
    have h₁ := mul_le_mul_of_nonneg_right (hk t ht)
      (mul_nonneg (by linarith : 0 ≤ 2-energy (q t) (y t)) hv)
    have h₂ := mul_nonneg (mul_nonneg hk₀.le (sub_nonneg.mpr hc)) hv
    nlinarith)
  intro t ht
  exact ⟨hcap t ht, by simpa only [neg_mul] using he t ht⟩

/-- The half-angle odds V/(2-V)=tan(theta/2)^2 have an exactly linear
ODE for the common observer, without a local Taylor approximation. -/
theorem odds_derivative {V : ℝ → ℝ} {k t : ℝ}
    (hd : HasDerivAt V (-k*(2-V t)*V t) t) (hV : V t ≠ 2) :
    HasDerivAt (fun s => V s/(2-V s)) (-2*k*(V t/(2-V t))) t := by
  have hn : 2-V t ≠ 0 := sub_ne_zero.mpr (Ne.symm hV)
  convert hd.div (hd.const_sub 2) hn using 1
  field_simp
  ring

theorem angle_odds (θ : ℝ) (hc : cos (θ/2) ≠ 0) :
    energy (BearingOutput.bearing 0) (BearingOutput.bearing θ) /
      (2-energy (BearingOutput.bearing 0) (BearingOutput.bearing θ)) = tan (θ/2)^2 := by
  have he : energy (BearingOutput.bearing 0) (BearingOutput.bearing θ) = 1-cos θ := by
    simp [energy, BearingOutput.bearing, dotProduct, Fin.sum_univ_succ]
  have hcos := cos_two_mul (θ/2)
  have hsin := sin_sq_add_cos_sq (θ/2)
  rw [show 2*(θ/2)=θ by ring] at hcos
  rw [he, show 2-(1-cos θ)=2*cos (θ/2)^2 by nlinarith,
    show 1-cos θ=2*sin (θ/2)^2 by nlinarith, tan_eq_sin_div_cos, div_pow]
  field_simp

/-- Exact finite-time common error law for constant gain. The preceding
cap theorem can discharge the non-antipodal-domain condition. -/
theorem odds_exact {V : ℝ → ℝ} {k a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt V (-k*(2-V t)*V t) t)
    (hV : ∀ t ∈ Icc a b, V t ≠ 2) :
    ∀ t ∈ Icc a b, V t/(2-V t) = V a/(2-V a)*exp (-2*k*(t-a)) := by
  have hw := fun t ht => odds_derivative (hd t ht) (hV t ht)
  have h₁ := Lyapunov.exponential_bound_on (c := 2*k) hw (by intro t ht; ring_nf; exact le_rfl)
  have h₂ := Lyapunov.exponential_bound_on (c := 2*k)
    (fun t ht => (hw t ht).neg) (by intro t ht; simp only [Pi.neg_apply]; ring_nf; exact le_rfl)
  intro t ht
  have hupper := h₁ t ht
  have hlower := h₂ t ht
  simp only [Pi.neg_apply, neg_mul] at hupper hlower ⊢
  linarith

/-- Connect the exact odds law to the actual physical observer and prove
its non-antipodal domain through the invariant cap. -/
theorem observer_odds_exact (ω q y : ℝ → Vec3) {k ρ a b : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ < 2) (hk : 0 < k)
    (hq : ∀ t ∈ Icc a b,
      HasDerivAt q (drift (ω t) (q t)+tangentCorrection k (q t) (y t)) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (drift (ω t) (y t)) t)
    (hqu : ∀ t ∈ Icc a b, q t ⬝ᵥ q t = 1)
    (hyu : ∀ t ∈ Icc a b, y t ⬝ᵥ y t = 1)
    (hinit : energy (q a) (y a) ≤ ρ) :
    ∀ t ∈ Icc a b, energy (q t) (y t)/(2-energy (q t) (y t)) =
      energy (q a) (y a)/(2-energy (q a) (y a))*exp (-2*k*(t-a)) := by
  have hc := observer_convergence ω q y (fun _ => k) hρ hρ2 hk
    (by intro t ht; exact le_rfl) hq hy hqu hyu hinit
  exact odds_exact (fun t ht => energy_derivative (hq t ht) (hy t ht) (hyu t ht))
    (fun t ht => ne_of_lt (lt_of_le_of_lt (hc t ht).1 hρ2))

theorem projection_norm_sq (q y : Vec3) (hq : q ⬝ᵥ q = 1) :
    enorm (BearingComparison.unitJacobian q y)^2 = enorm y^2-(q ⬝ᵥ y)^2 := by
  simpa only [enorm_sq, Axis.transverse, Axis.axial, BearingComparison.unitJacobian] using
    Axis.transverse_sq q y hq

theorem tangent_perturbation_supply (q y d : Vec3) {k D : ℝ}
    (hk : 0 < k) (hq : q ⬝ᵥ q = 1) (hy : y ⬝ᵥ y = 1)
    (htan : q ⬝ᵥ d = 0) (hd : enorm d ≤ D) :
    -k*(2-energy q y)*energy q y-d ⬝ᵥ y ≤
      -(k/2)*(2-energy q y)*energy q y+D^2/(2*k) := by
  have hs : enorm (BearingComparison.unitJacobian q y)^2 = (2-energy q y)*energy q y := by
    rw [projection_norm_sq q y hq, enorm_sq, ← dot_self_lengthSq, hy]
    dsimp [energy]
    ring
  have hdot : BearingComparison.unitJacobian q y ⬝ᵥ (-d) = -(d ⬝ᵥ y) := by
    simp [BearingComparison.unitJacobian, dotProduct_neg, sub_dotProduct,
      smul_dotProduct, htan, dotProduct_comm y d]
  have h := dot_young (BearingComparison.unitJacobian q y) (-d) hk
  rw [hdot, hs, enorm_neg] at h
  have hsq : enorm d^2 ≤ D^2 := by nlinarith [enorm_nonneg d]
  have hb := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 2*k)
  linarith

/-- Actual disturbed unit-bearing observer: a common certified error cap
and noise floor for both correction representations. All assumptions are
about physical ODEs, unit states and a bounded tangent perturbation. -/
theorem disturbed_observer_bound (ω q y d : ℝ → Vec3) {k D ρ a b : ℝ}
    (hk : 0 < k) (hρ : 0 < ρ) (hρ2 : ρ < 2)
    (hsmall : D^2 < k^2*ρ*(2-ρ))
    (hq : ∀ t ∈ Icc a b,
      HasDerivAt q (drift (ω t) (q t)+tangentCorrection k (q t) (y t)+d t) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (drift (ω t) (y t)) t)
    (hqu : ∀ t ∈ Icc a b, q t ⬝ᵥ q t = 1)
    (hyu : ∀ t ∈ Icc a b, y t ⬝ᵥ y t = 1)
    (htan : ∀ t ∈ Ico a b, q t ⬝ᵥ d t = 0)
    (hD : ∀ t ∈ Ico a b, enorm (d t) ≤ D)
    (hinit : energy (q a) (y a) ≤ ρ) :
    ∀ t ∈ Icc a b, energy (q t) (y t) ≤ ρ ∧
      energy (q t) (y t) ≤
        energy (q a) (y a)*exp (-(k*(2-ρ)/2)*(t-a))+
        (D^2/(k^2*(2-ρ)))*(1-exp (-(k*(2-ρ)/2)*(t-a))) := by
  have hd := fun t ht => perturbed_energy_derivative (hq t ht) (hy t ht) (hyu t ht)
  have hs := fun t ht => tangent_perturbation_supply (q t) (y t) (d t) hk
    (hqu t ⟨ht.1,ht.2.le⟩) (hyu t ⟨ht.1,ht.2.le⟩) (htan t ht) (hD t ht)
  have hbudget : D^2/(2*k) < (k/2)*(2-ρ)*ρ :=
    (div_lt_iff₀ (by positivity)).mpr (by nlinarith [hsmall])
  have hcap : ∀ t ∈ Icc a b, energy (q t) (y t) ≤ ρ := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
      hinit (fun t => hasDerivAt_const t ρ)
    intro t ht he
    have hh := hs t ht
    rw [he] at hh ⊢
    linarith
  have hrate : 0 < k*(2-ρ)/2 := div_pos (mul_pos hk (sub_pos.mpr hρ2)) (by norm_num)
  have he := Lyapunov.disturbed_bound_on (c := k*(2-ρ)/2) (ε := D^2/(2*k))
    hrate.ne' hd (by
      intro t ht
      have hv := energy_nonneg (q t) (y t) (hqu t ⟨ht.1,ht.2.le⟩) (hyu t ⟨ht.1,ht.2.le⟩)
      have hprod := mul_nonneg (mul_nonneg hk.le (sub_nonneg.mpr (hcap t ⟨ht.1,ht.2.le⟩))) hv
      nlinarith [hs t ht])
  intro t ht
  refine ⟨hcap t ht, ?_⟩
  convert he t ht using 1
  congr 1
  congr 1
  field_simp

/-- Measurement forcing and gyro mismatch have the same tangent budget
in either correction representation. -/
theorem sensor_perturbation (q ν v : Vec3) {k : ℝ} (hk : 0 ≤ k)
    (hq : q ⬝ᵥ q = 1) :
    q ⬝ᵥ (drift ν q+tangentCorrection k q v) = 0 ∧
      enorm (drift ν q+tangentCorrection k q v) ≤ enorm ν+k*enorm v := by
  constructor
  · simp [drift, add_dotProduct, correction_tangent k q v hq]
  · have hqn : enorm q = 1 := by
      have hs := enorm_sq q
      rw [← dot_self_lengthSq, hq] at hs
      nlinarith [enorm_nonneg q]
    have hp : enorm (BearingComparison.unitJacobian q v) ≤ enorm v := by
      have hs := projection_norm_sq q v hq
      nlinarith [sq_nonneg (q ⬝ᵥ v), enorm_nonneg v,
        enorm_nonneg (BearingComparison.unitJacobian q v)]
    have h₁ := cross_enorm_le ν q
    rw [hqn, mul_one] at h₁
    have h₂ := mul_le_mul_of_nonneg_left hp hk
    have ht := enorm_add_le (drift ν q) (tangentCorrection k q v)
    simp only [drift, enorm_neg, tangentCorrection, enorm_smul, abs_of_nonneg hk] at ht
    change k*enorm (v-(q ⬝ᵥ v) • q) ≤ k*enorm v at h₂
    exact ht.trans (add_le_add h₁ h₂)

theorem sensor_perturbation_identity (ω ν q y v : Vec3) (k : ℝ) :
    drift (ω+ν) q+tangentCorrection k q (y+v) =
      drift ω q+tangentCorrection k q y+(drift ν q+tangentCorrection k q v) := by
  ext i
  fin_cases i <;> simp [drift, tangentCorrection, crossProduct, dotProduct,
    Fin.sum_univ_succ, vecHead, vecTail] <;> ring

end GNC.BearingDynamics
