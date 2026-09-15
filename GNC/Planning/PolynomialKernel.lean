import GNC.Planning.DubinsPolynomial

/-! Executable polynomial arithmetic with a mathlib polynomial specification.
Coefficients are in ascending power order. Instantiating the algorithms at
`ℚ` gives exact executable arithmetic; their correctness does not depend on
testing, floating-point evaluation, or a source-language compiler.
-/
namespace GNC.Planning.PolynomialKernel

variable {K : Type*} [CommSemiring K]

/-- Horner evaluation, executable over any computable coefficient semiring. -/
def evaluate : List K → K → K
  | [], _ => 0
  | a :: rest, x => a + x * evaluate rest x

/-- The mathematical meaning of an ascending coefficient list. -/
noncomputable def polynomial : List K → Polynomial K
  | [] => 0
  | a :: rest => Polynomial.C a + Polynomial.X * polynomial rest

theorem evaluate_correct (cs : List K) (x : K) :
    evaluate cs x = (polynomial cs).eval x := by
  induction cs with
  | nil => simp [evaluate, polynomial]
  | cons a cs ih => simp [evaluate, polynomial, ih]

/-- Shared Horner evaluation of value and directional derivative. This is
forward AD for a polynomial, with the intermediate value reused. -/
def valueDerivative : List K → K → K × K
  | [], _ => (0,0)
  | [a], _ => (a,0)
  | a :: b :: rest, x =>
    let (v,d) := valueDerivative (b :: rest) x
    (a+x*v,v+x*d)

theorem valueDerivative_correct (cs : List K) (x : K) :
    valueDerivative cs x = ((polynomial cs).eval x,(polynomial cs).derivative.eval x) := by
  induction cs with
  | nil => simp [valueDerivative,polynomial]
  | cons a cs ih =>
    cases cs with
    | nil => simp [valueDerivative,polynomial]
    | cons b rest =>
      simp only [valueDerivative,ih]
      simp [polynomial,Polynomial.derivative_add,Polynomial.derivative_mul]

def weighted : ℕ → List K → List K
  | _, [] => []
  | n, a :: rest => (n : K) * a :: weighted (n + 1) rest

/-- Coefficients of the derivative, without constructing a polynomial. -/
def differentiate (cs : List K) : List K := weighted 1 cs.tail

theorem weighted_correct (cs : List K) (n : ℕ) :
    polynomial (weighted n cs) =
      Polynomial.C (n : K) * polynomial cs +
        Polynomial.X * (polynomial cs).derivative := by
  induction cs generalizing n with
  | nil => simp [weighted, polynomial]
  | cons a cs ih =>
    simp [weighted, polynomial, ih, Polynomial.derivative_add,
      Polynomial.derivative_mul, Nat.cast_add, Polynomial.C_add]
    ring

theorem differentiate_correct (cs : List K) :
    polynomial (differentiate cs) = (polynomial cs).derivative := by
  cases cs with
  | nil => simp [differentiate, polynomial, weighted]
  | cons a cs =>
    simp [differentiate, polynomial, weighted_correct, Polynomial.derivative_add,
      Polynomial.derivative_mul]

/-- Evaluate the derivative of order `n`; order zero is the value itself. -/
def jet (cs : List K) (x : K) : ℕ → K
  | 0 => evaluate cs x
  | n + 1 => jet (differentiate cs) x n

theorem jet_correct (cs : List K) (x : K) (n : ℕ) :
    jet cs x n = ((Polynomial.derivative^[n]) (polynomial cs)).eval x := by
  induction n generalizing cs with
  | zero => simp [jet, evaluate_correct]
  | succ n ih =>
    rw [jet, ih, differentiate_correct, Function.iterate_succ_apply]

theorem evaluate_map {L : Type*} [CommSemiring L] (f : K →+* L)
    (cs : List K) (x : K) :
    evaluate (cs.map f) (f x) = f (evaluate cs x) := by
  induction cs with
  | nil => simp [evaluate]
  | cons a cs ih => simp [evaluate, ih]

theorem weighted_map {L : Type*} [CommSemiring L] (f : K →+* L)
    (cs : List K) (n : ℕ) :
    weighted n (cs.map f) = (weighted n cs).map f := by
  induction cs generalizing n with
  | nil => rfl
  | cons a cs ih => simp [weighted, ih]

theorem differentiate_map {L : Type*} [CommSemiring L] (f : K →+* L)
    (cs : List K) :
    differentiate (cs.map f) = (differentiate cs).map f := by
  cases cs <;> simp [differentiate, weighted, weighted_map]

theorem jet_map {L : Type*} [CommSemiring L] (f : K →+* L)
    (cs : List K) (x : K) (n : ℕ) :
    jet (cs.map f) (f x) n = f (jet cs x n) := by
  induction n generalizing cs with
  | zero => exact evaluate_map f cs x
  | succ n ih => simp only [jet, differentiate_map, ih]

/-- The normalized Hermite seed, now as executable coefficients. -/
def seedCoefficients {F : Type*} [Field F] (a b : F) : List F :=
  [0, 0, a/2, 0, -5*a+5*b/2, 10*a-7*b, -15*a/2+13*b/2, 2*a-2*b]

theorem seed_correct (a b : ℝ) :
    polynomial (seedCoefficients a b) = DubinsPolynomial.seed a b := by
  simp [seedCoefficients, polynomial, DubinsPolynomial.seed,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_neg]
  ring

theorem seed_cast (a b : ℚ) :
    (seedCoefficients a b).map (Rat.castHom ℝ) =
      seedCoefficients (a : ℝ) (b : ℝ) := by
  simp [seedCoefficients]

/-- Every exact rational jet is the corresponding derivative of the real
Hermite polynomial. This theorem covers all inputs and derivative orders. -/
theorem rational_seed_jet (a b x : ℚ) (n : ℕ) :
    ((jet (seedCoefficients a b) x n : ℚ) : ℝ) =
      ((Polynomial.derivative^[n]) (DubinsPolynomial.seed a b)).eval (x : ℝ) := by
  have h := jet_map (Rat.castHom ℝ) (seedCoefficients a b) x n
  rw [seed_cast, jet_correct, seed_correct] at h
  exact h.symm

/-- Physical nominal-distance jet of `L² * seed(a,b)(q/L)`. -/
def physicalJet {F : Type*} [Field F] (a b L q : F) (n : ℕ) : F :=
  L^2 * jet (seedCoefficients a b) (q/L) n / L^n

theorem physicalJet_cast (a b L q : ℚ) (n : ℕ) :
    ((physicalJet a b L q n : ℚ) : ℝ) = physicalJet (a : ℝ) b L q n := by
  have h := jet_map (Rat.castHom ℝ) (seedCoefficients a b) (q/L) n
  change jet ((seedCoefficients a b).map (Rat.castHom ℝ)) ((q/L : ℚ) : ℝ) n =
    ((jet (seedCoefficients a b) (q/L) n : ℚ) : ℝ) at h
  rw [seed_cast, Rat.cast_div] at h
  simp only [physicalJet, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, h]

theorem physicalJet_zero (a b L q : ℝ) :
    physicalJet a b L q 0 = L^2 * (DubinsPolynomial.seed a b).eval (q/L) := by
  simp [physicalJet, jet_correct, seed_correct]

/-- The executable rescaling computes actual derivatives in nominal distance,
including every order needed by acceleration, jerk and curvature commands. -/
theorem physicalJet_derivative (a b L q : ℝ) (hL : L ≠ 0) (n : ℕ) :
    HasDerivAt (fun s => physicalJet a b L s n)
      (physicalJet a b L q (n+1)) q := by
  have hpoly := (((Polynomial.derivative^[n]) (DubinsPolynomial.seed a b)).hasDerivAt
    (q/L)).scomp q ((hasDerivAt_id q).div_const L)
  convert (hpoly.const_mul (L^2)).div_const (L^n) using 1
  · simp [physicalJet, jet_correct, seed_correct]
  · simp only [physicalJet, jet_correct, seed_correct,
      Function.iterate_succ_apply', smul_eq_mul, pow_succ]
    field_simp

theorem rational_seed_endpoints (a b : ℚ) :
    jet (seedCoefficients a b) 0 0 = 0 ∧ jet (seedCoefficients a b) 1 0 = 0 ∧
    jet (seedCoefficients a b) 0 1 = 0 ∧ jet (seedCoefficients a b) 1 1 = 0 ∧
    jet (seedCoefficients a b) 0 2 = a ∧ jet (seedCoefficients a b) 1 2 = b ∧
    jet (seedCoefficients a b) 0 3 = 0 ∧ jet (seedCoefficients a b) 1 3 = 0 := by
  norm_num [jet, differentiate, weighted, seedCoefficients, evaluate]
  ring_nf
  simp

/-- The executable symmetric seed inherits the continuous regularity bound.
This controls the tangent's longitudinal factor throughout a segment, not
only at a finite list of evaluated distances. -/
theorem physicalJet_regular {k L q : ℚ} (hL : 0 < L) (hq : q ∈ Set.Icc 0 L) :
    1 ≤ 1 - k * physicalJet (-k) (-k) L q 0 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hqr : (q : ℝ) ∈ Set.Icc 0 (L : ℝ) :=
    ⟨by exact_mod_cast hq.1, by exact_mod_cast hq.2⟩
  have hu : (q : ℝ) / (L : ℝ) ∈ Set.Icc 0 1 :=
    ⟨div_nonneg hqr.1 hLr.le, (div_le_one hLr).mpr hqr.2⟩
  have h := DubinsPolynomial.seed_regular hu (k : ℝ) (L : ℝ)
  have hj := physicalJet_cast (-k) (-k) L q 0
  rw [physicalJet_zero] at hj
  push_cast at hj
  rw [← hj] at h
  exact_mod_cast h

end GNC.Planning.PolynomialKernel
