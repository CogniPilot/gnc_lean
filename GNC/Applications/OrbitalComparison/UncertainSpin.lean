import GNC.Dynamics.SpinningThrust
import GNC.Analysis.PolynomialObstruction
import Mathlib.Analysis.Real.Pi.Bounds

/-! Uncertain spin is a representation stress test, not a full nonlinear
orbit certificate. Seven exact phase extrema obstruct every quartic in
the uncertain rate, including best fits rather than just Taylor jets.
The retained expression is also available to classical analytic methods. -/
namespace GNC.OrbitalComparison.UncertainSpin
open Finset Set PolynomialObstruction SpinningThrust
noncomputable section

def phaseNodes : Fin 7 → ℚ := ![71/2,73/2,75/2,77/2,79/2,81/2,83/2]
def weights : Fin 7 → ℚ := ![71/4928,-438/4928,1125/4928,-1540/4928,
  1185/4928,-486/4928,83/4928]
def signs : Fin 7 → ℚ := ![-1,1,-1,1,-1,1,-1]
def rates (T : ℝ) (i : Fin 7) : ℝ := Real.pi / T * (phaseNodes i : ℝ)

theorem moments : ∀ k : Fin 5, ∑ i, weights i * phaseNodes i ^ k.val = 0 := by
  decide +kernel
theorem variation : ∑ i, |weights i| = 1 := by decide +kernel

theorem rate_moments (T : ℝ) {k : ℕ} (hk : k ≤ 4) :
    ∑ i, (weights i : ℝ) * rates T i ^ k = 0 := by
  have h : ∑ i, (weights i : ℝ) * (phaseNodes i : ℝ)^k = 0 := by
    exact_mod_cast moments ⟨k, by omega⟩
  calc
    _ = (Real.pi / T)^k * ∑ i, (weights i : ℝ) * (phaseNodes i : ℝ)^k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [rates, mul_pow]
      ring
    _ = 0 := by rw [h, mul_zero]

theorem phase_sines (i : Fin 7) :
    Real.sin (Real.pi * (phaseNodes i : ℝ)) = (signs i : ℝ) := by
  have h (n : ℕ) : Real.sin (Real.pi * ((n : ℝ)+1/2)) = (-1:ℝ)^n := by
    rw [show Real.pi*((n:ℝ)+1/2) = Real.pi/2+n*Real.pi by ring,
      Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one]
  have h35 := h 35
  have h36 := h 36
  have h37 := h 37
  have h38 := h 38
  have h39 := h 39
  have h40 := h 40
  have h41 := h 41
  norm_num at h35 h36 h37 h38 h39 h40 h41
  fin_cases i <;> norm_num [phaseNodes, signs] <;> assumption

theorem velocity_samples (a : ℝ) {T : ℝ} (hT : T ≠ 0) (i : Fin 7) :
    velocityX a (rates T i) T =
      a*T/Real.pi * ((signs i : ℝ)/(phaseNodes i : ℝ)) := by
  unfold velocityX
  rw [show rates T i*T = Real.pi*(phaseNodes i : ℝ) by
    unfold rates; field_simp, phase_sines]
  unfold rates
  field_simp
  <;> ring

theorem sample_signal (a : ℝ) {T : ℝ} (hT : T ≠ 0) :
    ∑ i, (weights i : ℝ) * velocityX a (rates T i) T =
      -(2*a*T/(77*Real.pi)) := by
  simp_rw [velocity_samples a hT]
  norm_num [Fin.sum_univ_succ, weights, signs, phaseNodes]
  ring

/-- A lower bound on every degree-four rate polynomial, not just a chosen
STT approximation. It scales with the transverse acceleration. -/
theorem quartic_lower_bound {a T ε : ℝ} (ha : 0 ≤ a) (hT : 0 < T)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ 4)
    (he : ∀ i, |velocityX a (rates T i) T-p.eval (rates T i)| ≤ ε) :
    2*a*T/(77*Real.pi) ≤ ε := by
  have hw : ∑ i, |(weights i : ℝ)| = 1 := by exact_mod_cast variation
  have h := error_lower_bound (rates T) (fun i => (weights i : ℝ))
    (fun i => velocityX a (rates T i) T) (fun i => velocityX a (rates T i) T)
    (fun _ => 0) (fun _ hk => rate_moments T hk) hw
    (fun _ => by simp) p hp he
  rw [sample_signal a hT.ne', abs_neg, abs_of_nonneg (by positivity)] at h
  simpa using h

theorem example_rates (i : Fin 7) : rates 1200 i ∈ Icc (9/100:ℝ) (11/100) := by
  have hl := Real.pi_gt_d2
  have hu := Real.pi_lt_d2
  fin_cases i <;> norm_num [rates, phaseNodes] <;> constructor <;> linarith

/-- A separately proved gravity/model discrepancy consumes the obstruction
budget explicitly. This hypothesis is not a certificate for any orbit. -/
theorem perturbed_quartic_lower_bound {a T ε δ : ℝ} (ha : 0 ≤ a) (hT : 0 < T)
    (physical : ℝ → ℝ) (p : Polynomial ℝ) (hp : p.natDegree ≤ 4)
    (hd : ∀ i, |physical (rates T i)-velocityX a (rates T i) T| ≤ δ)
    (he : ∀ i, |physical (rates T i)-p.eval (rates T i)| ≤ ε) :
    2*a*T/(77*Real.pi)-δ ≤ ε := by
  have hb := quartic_lower_bound ha hT p hp (ε := δ+ε) (fun i => by
    calc
      _ ≤ |velocityX a (rates T i) T-physical (rates T i)|+
          |physical (rates T i)-p.eval (rates T i)| := abs_sub_le _ _ _
      _ ≤ δ+ε := add_le_add (by rw [abs_sub_comm]; exact hd i) (he i))
  linarith

/-- For a=0.0001 m/s², T=1200 s and rate 0.09--0.11 rad/s, every
quartic has an error greater than 0.99 mm/s somewhere in the interval. -/
theorem example_quartic_obstruction (p : Polynomial ℝ) (hp : p.natDegree ≤ 4) :
    ∃ ω ∈ Icc (9/100:ℝ) (11/100),
      99/100000 < |velocityX (1/10000) ω 1200-p.eval ω| := by
  by_contra! h
  have hb := quartic_lower_bound (by norm_num : (0:ℝ) ≤ 1/10000)
    (by norm_num : (0:ℝ) < 1200) p hp (fun i => h _ (example_rates i))
  have hpi := Real.pi_lt_d4
  have hpos := Real.pi_pos
  have := (div_le_iff₀ (by positivity : (0:ℝ) < 77*Real.pi)).mp hb
  norm_num at this
  nlinarith

end
end GNC.OrbitalComparison.UncertainSpin
