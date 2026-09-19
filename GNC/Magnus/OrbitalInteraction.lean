import GNC.Magnus.BlockTerms

/-! Interaction-picture Magnus structure of the orbital variational equation.
The variational generator A(t) = drift + gravity (K t) has a nilpotent free-drift
part with drift^2 = 0, so exp(t . drift) = 1 + t . drift terminates exactly.
Conjugating the time-varying gravity gradient by this free-drift flow yields the
interaction generator L(t). Each L(t) is pointwise square-zero, but products and
commutators of L at different times do not vanish: the gravity gradient values do
not commute across time, so the interaction Magnus series does not terminate.
The convention is left evolution, Phi' = A Phi. -/
noncomputable section
open Matrix NormedSpace MeasureTheory
open scoped Matrix.Norms.Operator
open GNC.OrbitalNilpotence
namespace GNC.OrbitalInteraction
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Interval integral of a matrix commutes with entry extraction. -/
theorem integral_entry {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {F : ℝ → Matrix p q ℝ}
    {a b : ℝ} (i : p) (j : q) (hF : IntervalIntegrable F volume a b) :
    (∫ t in a..b, F t) i j = ∫ t in a..b, F t i j := by
  have := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.intervalIntegral_comp_comm hF
  simpa using this.symm

/-- Interval integral distributes over a 2x2 block decomposition. -/
theorem integral_fromBlocks {A B C D : ℝ → Matrix n n ℝ} {a b : ℝ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (hD : Continuous D) :
    (∫ t in a..b, fromBlocks (A t) (B t) (C t) (D t)) =
      fromBlocks (∫ t in a..b, A t) (∫ t in a..b, B t)
        (∫ t in a..b, C t) (∫ t in a..b, D t) := by
  have hFc : Continuous (fun t => fromBlocks (A t) (B t) (C t) (D t)) := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    rcases i with i | i <;> rcases j with j | j
    · exact (continuous_apply j).comp ((continuous_apply i).comp hA)
    · exact (continuous_apply j).comp ((continuous_apply i).comp hB)
    · exact (continuous_apply j).comp ((continuous_apply i).comp hC)
    · exact (continuous_apply j).comp ((continuous_apply i).comp hD)
  ext i j
  rw [integral_entry i j (hFc.intervalIntegrable a b)]
  rcases i with i | i <;> rcases j with j | j
  · simp only [fromBlocks_apply₁₁]; rw [integral_entry i j (hA.intervalIntegrable a b)]
  · simp only [fromBlocks_apply₁₂]; rw [integral_entry i j (hB.intervalIntegrable a b)]
  · simp only [fromBlocks_apply₂₁]; rw [integral_entry i j (hC.intervalIntegrable a b)]
  · simp only [fromBlocks_apply₂₂]; rw [integral_entry i j (hD.intervalIntegrable a b)]

/-- The free-drift flow is exact: exp(t . drift) = 1 + t . drift. -/
theorem exp_drift (t : ℝ) :
    exp (t • drift (n := n)) = fromBlocks 1 (t • (1 : Matrix n n ℝ)) 0 1 := by
  have h : t • drift (n := n) = NilpotentInteraction.lift (t • (1 : Matrix n n ℝ)) := by
    simp [drift, NilpotentInteraction.lift, fromBlocks_smul, smul_zero]
  rw [h, NilpotentInteraction.exponential]

/-- The interaction generator: gravity gradient conjugated by the free-drift flow. -/
def interaction (K : ℝ → Matrix n n ℝ) (t : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  (1 - t • drift) * gravity (K t) * (1 + t • drift)

/-- The rank-one time weight structure shared by the interaction products. -/
def productBlock (a b : ℝ) (M : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks (-(a • M)) (-((a * b) • M)) M (b • M)

omit [Fintype n] in
theorem one_add_drift (t : ℝ) :
    (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) + t • drift = fromBlocks 1 (t • (1 : Matrix n n ℝ)) 0 1 := by
  have h1 : (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = fromBlocks 1 0 0 1 := fromBlocks_one.symm
  rw [h1, drift, fromBlocks_smul, fromBlocks_add]
  simp [smul_zero]

omit [Fintype n] in
theorem one_sub_drift (t : ℝ) :
    (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) - t • drift =
      fromBlocks 1 (-(t • (1 : Matrix n n ℝ))) 0 1 := by
  have h1 : (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = fromBlocks 1 0 0 1 := fromBlocks_one.symm
  rw [h1, drift, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [smul_zero]

/-- Closed block form of the interaction generator. -/
theorem interaction_blocks (K : ℝ → Matrix n n ℝ) (t : ℝ) :
    interaction K t = fromBlocks (-(t • K t)) (-(t^2 • K t)) (K t) (t • K t) := by
  rw [interaction, one_sub_drift, one_add_drift, gravity, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul,
      add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.neg_mul, pow_two] <;>
    module

/-- Each interaction generator is square-zero at a fixed time. -/
theorem interaction_square (K : ℝ → Matrix n n ℝ) (t : ℝ) :
    interaction K t * interaction K t = 0 := by
  rw [interaction_blocks, fromBlocks_multiply, ← fromBlocks_zero, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, smul_neg, pow_two]; module)

/-- Two-time product of interaction generators: a rank-one gravity moment,
weighted by the time separation (s - t). The cross-time product is nonzero. -/
theorem interaction_product (K : ℝ → Matrix n n ℝ) (s t : ℝ) :
    interaction K s * interaction K t = (s - t) • productBlock s t (K s * K t) := by
  rw [interaction_blocks, interaction_blocks, fromBlocks_multiply, productBlock, fromBlocks_smul,
    fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, smul_neg, pow_two]; module)

/-- Commutator of interaction generators at two times, as a difference of the
two rank-one gravity moments (orders K s K t and K t K s do not agree). -/
theorem interaction_commutator (K : ℝ → Matrix n n ℝ) (s t : ℝ) :
    Magnus.comm (interaction K s) (interaction K t) =
      (s - t) • productBlock s t (K s * K t) - (t - s) • productBlock t s (K t * K s) := by
  rw [Magnus.comm, interaction_product, interaction_product]

omit [Fintype n] [DecidableEq n] in
/-- Continuity of the moment integrand t^k . K t along a continuous gradient. -/
theorem moment_integrand_continuous (K : ℝ → Matrix n n ℝ) (hK : Continuous K) (k : ℕ) :
    Continuous (fun t => t^k • K t) := (continuous_pow k).smul hK

/-- The (a, b) time moment of the gravity gradient. -/
def moment (K : ℝ → Matrix n n ℝ) (k : ℕ) (h : ℝ) : Matrix n n ℝ :=
  ∫ t in (0:ℝ)..h, t^k • K t

/-- The first Magnus integrand reduces to the moment integrals of the gradient. -/
theorem first_interaction (K : ℝ → Matrix n n ℝ) (hK : Continuous K) (h : ℝ) :
    BlockMagnus.first (fun t => interaction K t) h =
      fromBlocks (-(moment K 1 h)) (-(moment K 2 h)) (moment K 0 h) (moment K 1 h) := by
  rw [BlockMagnus.first]
  simp only [interaction_blocks]
  rw [integral_fromBlocks (A := fun t => -(t • K t)) (B := fun t => -(t^2 • K t))
      (C := fun t => K t) (D := fun t => t • K t)
      (by exact (continuous_id.smul hK).neg) (by exact ((continuous_pow 2).smul hK).neg)
      hK (by exact continuous_id.smul hK),
    intervalIntegral.integral_neg, intervalIntegral.integral_neg]
  simp only [moment, pow_one, pow_zero, one_smul]

/-- The second Magnus integrand, as a double integral of the two-time
commutator: the (t1 - t2) weighted difference of the rank-one gravity moments.
The scalar weights t1^a t2^b appear inside the productBlock factors. -/
theorem second_interaction (K : ℝ → Matrix n n ℝ) (h : ℝ) :
    BlockMagnus.second (fun t => interaction K t) h =
      (1/2 : ℝ) • ∫ t₁ in (0:ℝ)..h, ∫ t₂ in (0:ℝ)..t₁,
        ((t₁ - t₂) • productBlock t₁ t₂ (K t₁ * K t₂) -
          (t₂ - t₁) • productBlock t₂ t₁ (K t₂ * K t₁)) := by
  simp only [BlockMagnus.second, interaction_commutator]

theorem drift_mul_one_add (t : ℝ) :
    drift (n := n) * (1 + t • drift) = drift := by
  have hsq : drift (n := n) * drift = 0 := by
    have := (separate_squares (n := n) 0).1; rwa [pow_two] at this
  rw [mul_add, mul_one, mul_smul_comm, hsq, smul_zero, add_zero]

theorem one_add_mul_one_sub (t : ℝ) :
    ((1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) + t • drift) * (1 - t • drift) = 1 := by
  have hsq : drift (n := n) * drift = 0 := by
    have := (separate_squares (n := n) 0).1; rwa [pow_two] at this
  have expand : ((1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) + t • drift) * (1 - t • drift) =
      1 - (t * t) • (drift * drift) := by
    simp only [mul_sub, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, smul_add,
      smul_smul]
    abel
  rw [expand, hsq, smul_zero, sub_zero]

/-- The free-drift flow intertwines the interaction generator with the
gravity block: (1 + t . drift) L(t) = gravity (K t) (1 + t . drift). -/
theorem interaction_intertwine (K : ℝ → Matrix n n ℝ) (t : ℝ) :
    (1 + t • drift) * interaction K t = gravity (K t) * (1 + t • drift) := by
  rw [interaction, ← mul_assoc, ← mul_assoc, one_add_mul_one_sub, one_mul]

/-- Exact factorization of the original variational flow through the interaction
flow: if U solves U' = L U, then Phi = (1 + t . drift) U solves Phi' = A Phi with
A = drift + gravity (K t). -/
theorem interaction_factorization (K : ℝ → Matrix n n ℝ)
    {U : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hU : ∀ t, HasDerivAt U (interaction K t * U t) t) (t : ℝ) :
    HasDerivAt (fun s => (1 + s • drift) * U s)
      ((drift + gravity (K t)) * ((1 + t • drift) * U t)) t := by
  have hP : HasDerivAt (fun s => (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) + s • drift) drift t := by
    have := ((hasDerivAt_id t).smul_const (drift (n := n))).const_add
      (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    simpa using this
  have hprod := NilpotentInteraction.rectangular_derivative hP (hU t)
  convert hprod using 1
  rw [add_mul, ← mul_assoc, drift_mul_one_add]
  congr 1
  rw [← mul_assoc (1 + t • drift) (interaction K t) (U t), interaction_intertwine, mul_assoc]

/-- Concrete witness that the cross-time interaction product is nonzero: with a
constant unit gradient, L(0) L(1) does not vanish. Unlike the pure translation
lift, whose cross-time products all vanish, the interaction generators do not
annihilate across time, so the interaction Magnus series does not terminate. -/
theorem interaction_product_ne_zero :
    interaction (n := Fin 1) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 *
      interaction (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1 ≠ 0 := by
  intro hzero
  have he := congrArg (fun M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ =>
    M (Sum.inr 0) (Sum.inl 0)) hzero
  rw [interaction_product] at he
  simp [productBlock] at he

end GNC.OrbitalInteraction
