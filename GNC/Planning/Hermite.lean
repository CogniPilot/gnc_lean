import GNC.Planning.PolynomialKernel

/-! Executable septic Hermite interpolation. Endpoint data are values and
derivatives through order three, not power-series coefficients. The explicit
inverse avoids a numerical linear solve. All arithmetic theorems hold over
any characteristic-zero field, including both exact rationals and reals.
-/
namespace GNC.Planning.Hermite

set_option maxHeartbeats 1000000

open PolynomialKernel
variable {K : Type*} [Field K] [CharZero K]

/-- Ascending power coefficients, including trailing zeros. -/
def powerList (c : Fin 8 → K) : List K :=
  [c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7]

/-- Unique normalized septic with the prescribed jets at zero and one. -/
def normalized (start finish : Fin 4 → K) : Fin 8 → K :=
  let d₀ := finish 0 - (start 0 + start 1 + start 2 / 2 + start 3 / 6)
  let d₁ := finish 1 - (start 1 + start 2 + start 3 / 2)
  let d₂ := finish 2 - (start 2 + start 3)
  let d₃ := finish 3 - start 3
  ![start 0, start 1, start 2 / 2, start 3 / 6,
    35*d₀ - 15*d₁ + 5*d₂/2 - d₃/6,
    -84*d₀ + 39*d₁ - 7*d₂ + d₃/2,
    70*d₀ - 34*d₁ + 13*d₂/2 - d₃/2,
    -20*d₀ + 10*d₁ - 2*d₂ + d₃/6]

theorem normalized_start (start finish : Fin 4 → K) (n : Fin 4) :
    jet (powerList (normalized start finish)) 0 n = start n := by
  fin_cases n <;>
    dsimp [normalized, powerList, jet, differentiate, weighted, evaluate] <;> ring

theorem normalized_finish (start finish : Fin 4 → K) (n : Fin 4) :
    jet (powerList (normalized start finish)) 1 n = finish n := by
  fin_cases n <;>
    dsimp [normalized, powerList, jet, differentiate, weighted, evaluate] <;> ring

/-- Reconstructing any eight-coefficient polynomial from its endpoint jets
returns the original coefficients. This is also an explicit inverse proof. -/
theorem normalized_recover (c : Fin 8 → K) :
    normalized (fun n : Fin 4 => jet (powerList c) 0 n)
      (fun n : Fin 4 => jet (powerList c) 1 n) = c := by
  funext i
  fin_cases i <;>
    dsimp [normalized, powerList, jet, differentiate, weighted, evaluate] <;> ring

/-- A solver or translated function returning eight coefficients is correct
as soon as it satisfies the eight endpoint equations. -/
theorem normalized_unique (start finish : Fin 4 → K) (c : Fin 8 → K)
    (hstart : ∀ n : Fin 4, jet (powerList c) 0 n = start n)
    (hfinish : ∀ n : Fin 4, jet (powerList c) 1 n = finish n) :
    c = normalized start finish := by
  rw [← normalized_recover c, funext hstart, funext hfinish]

/-- Normalize physical nominal-distance endpoint derivatives using L^n. -/
def coefficients (start finish : Fin 4 → K) (L : K) : List K :=
  powerList (normalized (fun n => L^(n : ℕ) * start n)
    (fun n => L^(n : ℕ) * finish n))

/-- Derivative of order n in physical nominal distance q, not arc length. -/
def physicalJet (start finish : Fin 4 → K) (L q : K) (n : ℕ) : K :=
  jet (coefficients start finish L) (q/L) n / L^n

theorem physical_start (start finish : Fin 4 → K) (L : K) (hL : L ≠ 0)
    (n : Fin 4) : physicalJet start finish L 0 n = start n := by
  simp only [physicalJet, coefficients, zero_div, normalized_start]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hL)

theorem physical_finish (start finish : Fin 4 → K) (L : K) (hL : L ≠ 0)
    (n : Fin 4) : physicalJet start finish L L n = finish n := by
  simp only [physicalJet, coefficients, div_self hL, normalized_finish]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hL)

/-- Uniqueness also holds for physical derivative constraints on any nonzero
interval. The returned coefficients use the normalized coordinate q/L. -/
theorem physical_unique (start finish : Fin 4 → K) (L : K) (hL : L ≠ 0)
    (c : Fin 8 → K)
    (hstart : ∀ n : Fin 4, jet (powerList c) 0 n / L^(n : ℕ) = start n)
    (hfinish : ∀ n : Fin 4, jet (powerList c) 1 n / L^(n : ℕ) = finish n) :
    powerList c = coefficients start finish L := by
  have hc := normalized_unique (fun n => L^(n : ℕ) * start n)
    (fun n => L^(n : ℕ) * finish n) c
    (fun n => by
      simpa only [mul_comm] using (div_eq_iff (pow_ne_zero _ hL)).mp (hstart n))
    (fun n => by
      simpa only [mul_comm] using (div_eq_iff (pow_ne_zero _ hL)).mp (hfinish n))
  exact congrArg powerList hc

/-- Exact rational coefficients have the stated meaning over the reals. -/
theorem coefficients_cast (start finish : Fin 4 → ℚ) (L : ℚ) :
    (coefficients start finish L).map (Rat.castHom ℝ) =
      coefficients (fun i => (start i : ℝ)) (fun i => (finish i : ℝ)) (L : ℝ) := by
  dsimp [coefficients, powerList, normalized]
  push_cast
  rfl

theorem physicalJet_cast (start finish : Fin 4 → ℚ) (L q : ℚ) (n : ℕ) :
    ((physicalJet start finish L q n : ℚ) : ℝ) =
      physicalJet (fun i => (start i : ℝ)) (fun i => (finish i : ℝ)) L q n := by
  have h := jet_map (Rat.castHom ℝ) (coefficients start finish L) (q/L) n
  change jet ((coefficients start finish L).map (Rat.castHom ℝ)) ((q/L : ℚ) : ℝ) n =
    ((jet (coefficients start finish L) (q/L) n : ℚ) : ℝ) at h
  rw [coefficients_cast, Rat.cast_div] at h
  simp only [physicalJet, Rat.cast_div, Rat.cast_pow, h]

/-- Actual real derivatives at every order, including the chain-rule powers
of interval length required by the executable physical-distance evaluator. -/
theorem physicalJet_derivative (start finish : Fin 4 → ℝ) (L q : ℝ)
    (hL : L ≠ 0) (n : ℕ) :
    HasDerivAt (fun s => physicalJet start finish L s n)
      (physicalJet start finish L q (n+1)) q := by
  have hpoly := (((Polynomial.derivative^[n])
    (polynomial (coefficients start finish L))).hasDerivAt (q/L)).scomp q
      ((hasDerivAt_id q).div_const L)
  convert hpoly.div_const (L^n) using 1
  · simp [physicalJet, jet_correct]
  · simp only [physicalJet, jet_correct, Function.iterate_succ_apply',
      smul_eq_mul, pow_succ]
    field_simp

/-- The earlier zero-offset seed is a specialization of the general solver. -/
theorem normalized_seed (a b : K) :
    powerList (normalized ![0, 0, a, 0] ![0, 0, b, 0]) = seedCoefficients a b := by
  simp [powerList, normalized, seedCoefficients]
  ring_nf
  simp

end GNC.Planning.Hermite
