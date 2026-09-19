import GNC.Applications.CertifiedCoast.Curvature.Step

/-! Composition of certified curvature-certificate coast steps into a whole
orbit error bound. Each `StepRecord` carries a local transition candidate
`Ψ_j` evaluated at the step endpoint (`Pev_j`), whose exact rational products
`Φ_ij = Pev_i · Pev_{i-1} · ⋯ · Pev_j` transport the accumulated forcing of
step `j` to node `i`. The rational composition `stmQ` mirrors the real
composition `GNC.Transported.stm` and casts onto it, so the per-pair Frobenius
bounds stored in the record certify the real hypotheses of
`GNC.Transported.chain_bound_kernel_rows`. Sequentially closing each step tube
with `StepRecord.tube_sound` and reading off the composed node bound yields a
terminal error bound for every true inverse-square solution seeded within the
initial radii. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Finset Matrix
open GNC.Planning.PolynomialKernel GNC.PolynomialBounds
namespace GNC.Applications.CertifiedCoast.Curvature
open GNC.PlanarCoast GNC.PlanarCoast.Candidate GNC.PlanarCoast.CurvatureCandidate

/-! ### The rational composed transition -/

/-- The rational composed transition `stmQ P i j = P i * P (i-1) * ... * P j`,
mirroring `GNC.Transported.stm` over the rationals, with `stmQ P i j = 1`
whenever `i < j`. -/
def stmQ (P : ℕ → Matrix (Fin 4) (Fin 4) ℚ) : ℕ → ℕ → Matrix (Fin 4) (Fin 4) ℚ
  | 0, j => if 0 < j then 1 else P 0
  | (i + 1), j => if i + 1 < j then 1 else P (i + 1) * stmQ P i j

theorem stmQ_succ (P : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (i j : ℕ) (h : j ≤ i + 1) :
    stmQ P (i + 1) j = P (i + 1) * stmQ P i j := by
  simp only [stmQ, if_neg (Nat.not_lt.mpr h)]

/-- Matrix product commutes with the rational cast. -/
theorem map_cast_mul (A B : Matrix (Fin 4) (Fin 4) ℚ) :
    (A * B).map (Rat.cast : ℚ → ℝ) = A.map (Rat.cast) * B.map (Rat.cast) := by
  have := (Rat.castHom ℝ).mapMatrix.map_mul A B
  simpa [RingHom.mapMatrix_apply] using this

theorem map_cast_one : ((1 : Matrix (Fin 4) (Fin 4) ℚ).map (Rat.cast : ℚ → ℝ)) = 1 :=
  Matrix.map_one _ (by norm_num) (by norm_num)

/-- The cast of the rational composed transition is the real composed
transition of the casts. -/
theorem stmQ_cast (P : ℕ → Matrix (Fin 4) (Fin 4) ℚ) (i j : ℕ) :
    (stmQ P i j).map (Rat.cast : ℚ → ℝ)
      = GNC.Transported.stm (fun k => (P k).map (Rat.cast)) i j := by
  induction i with
  | zero =>
    simp only [stmQ, GNC.Transported.stm]
    by_cases h : 0 < j
    · simp [h]
    · simp [h]
  | succ i ih =>
    simp only [stmQ, GNC.Transported.stm]
    by_cases h : i + 1 < j
    · simp [h]
    · rw [if_neg h, if_neg h, map_cast_mul, ih]

/-! ### Rational Frobenius bounds restricted to row sets -/

/-- A rational square witness on a row block bounds the real row Frobenius
norm of the cast matrix. -/
theorem frobRows_map_cast_le (R : Finset (Fin 4)) (C : Matrix (Fin 4) (Fin 4) ℚ)
    {B : ℚ} (hsum : ∑ i ∈ R, ∑ j, (C i j) ^ 2 ≤ B ^ 2) (hB : 0 ≤ B) :
    GNC.Transported.frobRows R (C.map (Rat.cast : ℚ → ℝ)) ≤ (B : ℝ) := by
  rw [GNC.Transported.frobRows, Real.sqrt_le_iff]
  refine ⟨by exact_mod_cast hB, ?_⟩
  have hcast : (∑ i ∈ R, ∑ j, ((C.map (Rat.cast)) i j) ^ 2)
      = (((∑ i ∈ R, ∑ j, (C i j) ^ 2 : ℚ)) : ℝ) := by
    push_cast [Matrix.map_apply]; ring
  rw [hcast]
  calc (((∑ i ∈ R, ∑ j, (C i j) ^ 2 : ℚ)) : ℝ) ≤ ((B ^ 2 : ℚ) : ℝ) := by exact_mod_cast hsum
    _ = (B : ℝ) ^ 2 := by push_cast; ring

/-- A rational square witness on a row and column block bounds the real
row-and-column Frobenius norm of the cast matrix. -/
theorem frobRowsCols_map_cast_le (R C : Finset (Fin 4)) (Cm : Matrix (Fin 4) (Fin 4) ℚ)
    {B : ℚ} (hsum : ∑ i ∈ R, ∑ j ∈ C, (Cm i j) ^ 2 ≤ B ^ 2) (hB : 0 ≤ B) :
    GNC.Transported.frobRowsCols R C (Cm.map (Rat.cast : ℚ → ℝ)) ≤ (B : ℝ) := by
  rw [GNC.Transported.frobRowsCols, Real.sqrt_le_iff]
  refine ⟨by exact_mod_cast hB, ?_⟩
  have hcast : (∑ i ∈ R, ∑ j ∈ C, ((Cm.map (Rat.cast)) i j) ^ 2)
      = (((∑ i ∈ R, ∑ j ∈ C, (Cm i j) ^ 2 : ℚ)) : ℝ) := by
    push_cast [Matrix.map_apply]; ring
  rw [hcast]
  calc (((∑ i ∈ R, ∑ j ∈ C, (Cm i j) ^ 2 : ℚ)) : ℝ) ≤ ((B ^ 2 : ℚ) : ℝ) := by exact_mod_cast hsum
    _ = (B : ℝ) ^ 2 := by push_cast; ring

/-- Coefficient-sum Frobenius square restricted to a row block. -/
def matSumSqRows (P : PolyMat) (h : ℚ) (R : Finset (Fin 4)) : ℚ :=
  ∑ i ∈ R, ∑ j, (bound (P i j) h) ^ 2

/-- Coefficient-sum Frobenius square restricted to a row block and the
velocity columns `2, 3`. -/
def matSumSqRowsVel (P : PolyMat) (h : ℚ) (R : Finset (Fin 4)) : ℚ :=
  ∑ i ∈ R, ∑ j ∈ ({2, 3} : Finset (Fin 4)), (bound (P i j) h) ^ 2

theorem matSumSqRows_frobRows (P : PolyMat) {t : ℝ} {h : ℚ} (ht : |t| ≤ (h : ℝ))
    (R : Finset (Fin 4)) (B : ℚ) (hB : matSumSqRows P h R ≤ B ^ 2) (hB0 : 0 ≤ B) :
    GNC.Transported.frobRows R (realMat P t) ≤ (B : ℝ) := by
  rw [GNC.Transported.frobRows, Real.sqrt_le_iff]
  refine ⟨by exact_mod_cast hB0, ?_⟩
  have hle : ∑ i ∈ R, ∑ j, (realMat P t i j) ^ 2
      ≤ ∑ i ∈ R, ∑ j, ((bound (P i j) h : ℚ) : ℝ) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hev : |ev (P i j) t| ≤ ((bound (P i j) h : ℚ) : ℝ) := ev_abs_le _ ht
    simp only [realMat]
    nlinarith [abs_nonneg (ev (P i j) t), sq_abs (ev (P i j) t),
      (abs_nonneg (ev (P i j) t)).trans hev]
  refine hle.trans ?_
  have hcast : (∑ i ∈ R, ∑ j, ((bound (P i j) h : ℚ) : ℝ) ^ 2)
      = ((matSumSqRows P h R : ℚ) : ℝ) := by unfold matSumSqRows; push_cast; ring
  rw [hcast]
  calc ((matSumSqRows P h R : ℚ) : ℝ) ≤ ((B ^ 2 : ℚ) : ℝ) := by exact_mod_cast hB
    _ = (B : ℝ) ^ 2 := by push_cast; ring

theorem matSumSqRowsVel_frobRowsVel (P : PolyMat) {t : ℝ} {h : ℚ} (ht : |t| ≤ (h : ℝ))
    (R : Finset (Fin 4)) (B : ℚ) (hB : matSumSqRowsVel P h R ≤ B ^ 2) (hB0 : 0 ≤ B) :
    GNC.Transported.frobRowsVel R (realMat P t) ≤ (B : ℝ) := by
  rw [GNC.Transported.frobRowsVel, Real.sqrt_le_iff]
  refine ⟨by exact_mod_cast hB0, ?_⟩
  have hle : ∑ i ∈ R, ∑ j ∈ ({2, 3} : Finset (Fin 4)), (realMat P t i j) ^ 2
      ≤ ∑ i ∈ R, ∑ j ∈ ({2, 3} : Finset (Fin 4)), ((bound (P i j) h : ℚ) : ℝ) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hev : |ev (P i j) t| ≤ ((bound (P i j) h : ℚ) : ℝ) := ev_abs_le _ ht
    simp only [realMat]
    nlinarith [abs_nonneg (ev (P i j) t), sq_abs (ev (P i j) t),
      (abs_nonneg (ev (P i j) t)).trans hev]
  refine hle.trans ?_
  have hcast : (∑ i ∈ R, ∑ j ∈ ({2, 3} : Finset (Fin 4)), ((bound (P i j) h : ℚ) : ℝ) ^ 2)
      = ((matSumSqRowsVel P h R : ℚ) : ℝ) := by unfold matSumSqRowsVel; push_cast; ring
  rw [hcast]
  calc ((matSumSqRowsVel P h R : ℚ) : ℝ) ≤ ((B ^ 2 : ℚ) : ℝ) := by exact_mod_cast hB
    _ = (B : ℝ) ^ 2 := by push_cast; ring

/-- Tight per-pair velocity-column kernel bridge. A rational coefficient-sum
witness on the polynomial product `cMul Φ_ij H_j` (rows `R`, velocity columns)
bounds the real velocity-column Frobenius norm of the composed kernel
`(stm P i j) · H_j(s)` uniformly on the step, transporting the accumulated
forcing by the composed kernel itself rather than by a product of norms. -/
theorem stm_frobRowsVel_kernel_le (S : ℕ → StepRecord) (R : Finset (Fin 4)) (i j : ℕ)
    (Hpm : PolyMat) {s : ℝ} {h : ℚ} (hs : |s| ≤ (h : ℝ)) (B : ℚ) (hnn : 0 ≤ B)
    (hsum : matSumSqRowsVel (GNC.PlanarCoast.cMul (stmQ (fun k => (S k).Pev) i j) Hpm) h R ≤ B ^ 2) :
    GNC.Transported.frobRowsVel R
        (GNC.Transported.stm (fun k => ((S k).Pev).map (Rat.cast : ℚ → ℝ)) i j * realMat Hpm s)
      ≤ (B : ℝ) := by
  have hb := matSumSqRowsVel_frobRowsVel
    (GNC.PlanarCoast.cMul (stmQ (fun k => (S k).Pev) i j) Hpm) hs R B hsum hnn
  rw [GNC.PlanarCoast.realMat_cMul] at hb
  have hcast : (⇑(Rat.castHom ℝ) : ℚ → ℝ) = (Rat.cast : ℚ → ℝ) := rfl
  rw [hcast, stmQ_cast] at hb
  exact hb

/-! ### Frobenius submultiplicativity for the composed kernel bounds

The composed kernel norms are bounded submultiplicatively: the row-restricted
Frobenius norm of a product is at most the row-restricted norm of the left
factor times the (velocity-column) Frobenius norm of the right factor. This
charges the composition `Φ_ij H_j` by the composed transition size `Φ_ij` and
the per-step kernel norm `H_j`, without recomputing the high-degree product. -/

theorem frobRows_mul_le (R : Finset (Fin 4)) (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    GNC.Transported.frobRows R (A * B)
      ≤ GNC.Transported.frobRows R A * GNC.Transported.frob B := by
  rw [GNC.Transported.frobRows, GNC.Transported.frobRows, GNC.Transported.frob,
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hcs : ∀ i, ∑ j, ((A * B) i j) ^ 2 ≤ (∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (B k j) ^ 2) := by
    intro i
    calc ∑ j, ((A * B) i j) ^ 2
        = ∑ j, (∑ k, A i k * B k j) ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_; rw [Matrix.mul_apply]
      _ ≤ ∑ j, (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2) :=
          Finset.sum_le_sum fun j _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (B k j) ^ 2) := by rw [Finset.mul_sum]
  calc ∑ i ∈ R, ∑ j, ((A * B) i j) ^ 2
      ≤ ∑ i ∈ R, (∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (B k j) ^ 2) := Finset.sum_le_sum fun i _ => hcs i
    _ = (∑ i ∈ R, ∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (B k j) ^ 2) := by rw [Finset.sum_mul]
    _ = (∑ i ∈ R, ∑ j, (A i j) ^ 2) * (∑ i, ∑ j, (B i j) ^ 2) := by
        rw [show (∑ j, ∑ k, (B k j) ^ 2) = (∑ i, ∑ j, (B i j) ^ 2) from Finset.sum_comm]

theorem frobRowsVel_mul_le (R : Finset (Fin 4)) (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    GNC.Transported.frobRowsVel R (A * B)
      ≤ GNC.Transported.frobRows R A * GNC.Transported.frobVel B := by
  rw [GNC.Transported.frobRowsVel, GNC.Transported.frobRows, GNC.Transported.frobVel,
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hcs : ∀ i, ∑ j ∈ ({2, 3} : Finset (Fin 4)), ((A * B) i j) ^ 2
      ≤ (∑ k, (A i k) ^ 2) * (∑ j ∈ ({2, 3} : Finset (Fin 4)), ∑ k, (B k j) ^ 2) := by
    intro i
    calc ∑ j ∈ ({2, 3} : Finset (Fin 4)), ((A * B) i j) ^ 2
        = ∑ j ∈ ({2, 3} : Finset (Fin 4)), (∑ k, A i k * B k j) ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_; rw [Matrix.mul_apply]
      _ ≤ ∑ j ∈ ({2, 3} : Finset (Fin 4)), (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2) :=
          Finset.sum_le_sum fun j _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ k, (A i k) ^ 2) * (∑ j ∈ ({2, 3} : Finset (Fin 4)), ∑ k, (B k j) ^ 2) := by
          rw [Finset.mul_sum]
  calc ∑ i ∈ R, ∑ j ∈ ({2, 3} : Finset (Fin 4)), ((A * B) i j) ^ 2
      ≤ ∑ i ∈ R, (∑ k, (A i k) ^ 2) * (∑ j ∈ ({2, 3} : Finset (Fin 4)), ∑ k, (B k j) ^ 2) :=
        Finset.sum_le_sum fun i _ => hcs i
    _ = (∑ i ∈ R, ∑ k, (A i k) ^ 2) * (∑ j ∈ ({2, 3} : Finset (Fin 4)), ∑ k, (B k j) ^ 2) := by
        rw [Finset.sum_mul]
    _ = (∑ i ∈ R, ∑ j, (A i j) ^ 2) * (∑ i, ∑ j ∈ ({2, 3} : Finset (Fin 4)), (B i j) ^ 2) := by
        rw [show (∑ j ∈ ({2, 3} : Finset (Fin 4)), ∑ k, (B k j) ^ 2)
          = (∑ i, ∑ j ∈ ({2, 3} : Finset (Fin 4)), (B i j) ^ 2) from Finset.sum_comm]

/-! ### Real evaluation of a rational coefficient list -/

theorem ev_ratEval (cs : List ℚ) (t : ℚ) : ev cs (t : ℝ) = ((evaluate cs t : ℚ) : ℝ) := by
  rw [ev]; simpa using evaluate_map (Rat.castHom ℝ) cs t

/-! ### `join2` and row-projection norm relations -/

theorem join2_right_zero_norm (x : E2) : ‖join2 x (0 : E2)‖ = ‖x‖ := by
  have h : ‖join2 x (0 : E2)‖ ^ 2 = ‖x‖ ^ 2 := by rw [join2_norm_sq]; simp
  have hc := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hc

theorem join2_norm_le (x y : E2) : ‖join2 x y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖join2 x y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    rw [join2_norm_sq]; nlinarith [norm_nonneg x, norm_nonneg y]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- A stacked state with zero velocity part has vanishing velocity coordinates. -/
theorem join2_right_zero_apply (x : E2) (j : Fin 4)
    (hj : j ∉ ({0, 1} : Finset (Fin 4))) : (join2 x (0 : E2)) j = 0 := by
  fin_cases j <;> simp_all [join2, pack4]

/-- A stacked state with zero position part has vanishing position coordinates. -/
theorem join2_left_zero_apply (y : E2) (j : Fin 4)
    (hj : j ∉ ({2, 3} : Finset (Fin 4))) : (join2 (0 : E2) y) j = 0 := by
  fin_cases j <;> simp_all [join2, pack4]

theorem projRows_diag_component (R : Finset (Fin 4)) (v : GNC.Transported.E) (i : Fin 4) :
    (GNC.Transported.projRows R v) i = (if i ∈ R then (1:ℝ) else 0) * v i := by
  rw [GNC.Transported.projRows, GNC.Transported.act_component]
  rw [Finset.sum_eq_single i]
  · rw [GNC.Transported.diagRows, Matrix.diagonal_apply_eq]
  · intro j _ hj; rw [GNC.Transported.diagRows, Matrix.diagonal_apply_ne _ (Ne.symm hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Projecting a stacked state onto the position rows keeps the position part. -/
theorem projRows_pos (x y : E2) :
    GNC.Transported.projRows ({0, 1} : Finset (Fin 4)) (join2 x y) = join2 x (0 : E2) := by
  ext i
  rw [projRows_diag_component]
  fin_cases i <;>
    simp [join2, pack4, Finset.mem_insert, Finset.mem_singleton]

theorem projRows_vel (x y : E2) :
    GNC.Transported.projRows ({2, 3} : Finset (Fin 4)) (join2 x y) = join2 (0 : E2) y := by
  ext i
  rw [projRows_diag_component]
  fin_cases i <;>
    simp [join2, pack4, Finset.mem_insert, Finset.mem_singleton]

/-! ### Per-step ingredients for the composed chain

The composed chain bound `GNC.Transported.chain_bound_kernel_rows` consumes, per
step, the same transported error dynamics that `StepRecord.tube_sound` closes.
The following curves and lemmas expose those ingredients so the chain assembly
can telescope the exact step identity `step_identity` across the whole orbit. -/

namespace StepRecord

/-- The symplectic-transpose transition matrix curve `H_j = realMat H`. -/
def HfC (r : StepRecord) : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => realMat r.cc.H s
/-- The linearized state matrix curve `A_j(s) = Amat (pos s)`. -/
def AfC (r : StepRecord) : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => Amat (r.cc.pos s)
/-- The polynomial gradient candidate curve `Â_j = realMat (Ahat)`. -/
def AhfC (r : StepRecord) : ℝ → Matrix (Fin 4) (Fin 4) ℝ :=
  fun s => realMat (Ahat r.cc.toCandidate) s
/-- The derivative of the symplectic transition curve `H_j' = realMat (pDeriv H)`. -/
def HpfC (r : StepRecord) : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => realMat (pDeriv r.cc.H) s
/-- The transported error curve of the step for a true solution `w`. -/
def efC (r : StepRecord) (w : ℝ → Fin 4 → ℝ) : ℝ → GNC.Transported.E :=
  fun s => join2 (truePos w s - r.cc.pos s) (trueVel w s - r.cc.dpos s)
/-- The forcing curve of the step, supported on the velocity components. -/
def nfC (r : StepRecord) (w : ℝ → Fin 4 → ℝ) : ℝ → GNC.Transported.E :=
  fun s => join2 (0 : E2)
    (Gravity.field 1 (truePos w s) - r.cc.acc s
      - GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s))

theorem nfC_zero0 (r : StepRecord) (w : ℝ → Fin 4 → ℝ) (s : ℝ) : (r.nfC w s) 0 = 0 := rfl
theorem nfC_zero1 (r : StepRecord) (w : ℝ → Fin 4 → ℝ) (s : ℝ) : (r.nfC w s) 1 = 0 := rfl

theorem AfC_sub_AhfC_row0 (r : StepRecord) (s : ℝ) (k : Fin 4) :
    (r.AfC s - r.AhfC s) 0 k = 0 := Amat_sub_Ahat_row0 r.cc (r.cc.pos s) s k
theorem AfC_sub_AhfC_row1 (r : StepRecord) (s : ℝ) (k : Fin 4) :
    (r.AfC s - r.AhfC s) 1 k = 0 := Amat_sub_Ahat_row1 r.cc (r.cc.pos s) s k

/-- The transported error curve is differentiable with the linearized drift as
its derivative. -/
theorem efC_hasDerivAt (r : StepRecord) (w : ℝ → Fin 4 → ℝ) {s : ℝ}
    (hw : HasDerivAt w (PolynomialOrbit.physicalRate 0 (w s)) s) :
    HasDerivAt (r.efC w) (GNC.Transported.act (r.AfC s) (r.efC w s) + r.nfC w s) s := by
  have hd := join2_hasDerivAt (r.cc.toCandidate.errorPos_hasDerivAt hw)
    (r.cc.toCandidate.errorVel_hasDerivAt hw)
  have heq : GNC.Transported.act (r.AfC s) (r.efC w s) + r.nfC w s
      = join2 (trueVel w s - r.cc.dpos s) (Gravity.field 1 (truePos w s) - r.cc.acc s) := by
    show GNC.Transported.act (Amat (r.cc.pos s))
        (join2 (truePos w s - r.cc.pos s) (trueVel w s - r.cc.dpos s)) + r.nfC w s = _
    rw [act_eq, act_Amat]
    show join2 (trueVel w s - r.cc.dpos s) _
        + join2 (0 : E2) _ = _
    rw [join2_add]; congr 1 <;> abel
  rw [heq]; exact hd

theorem efC_continuous (r : StepRecord) {w : ℝ → Fin 4 → ℝ} (hwc : Continuous w) :
    Continuous (r.efC w) :=
  join2_continuous ((truePos_continuous hwc).sub r.cc.toCandidate.pos_continuous)
    ((trueVel_continuous hwc).sub r.cc.toCandidate.dpos_continuous)

/-- The transported drift of the step is continuous. -/
theorem driftC_continuous (r : StepRecord) {w : ℝ → Fin 4 → ℝ} (hwc : Continuous w)
    (hacc : Continuous (fun s => Gravity.field 1 (truePos w s))) :
    Continuous (GNC.Transported.drift r.HfC r.AfC r.HpfC (r.efC w) (r.nfC w)) := by
  have hce : Continuous (r.efC w) := r.efC_continuous hwc
  have hdrift : GNC.Transported.drift r.HfC r.AfC r.HpfC (r.efC w) (r.nfC w)
      = fun s => GNC.Transported.act (r.HpfC s) (r.efC w s)
          + GNC.Transported.act (r.HfC s)
              (join2 (trueVel w s - r.cc.dpos s) (Gravity.field 1 (truePos w s) - r.cc.acc s)) := by
    funext s
    have hedot : join2 (trueVel w s - r.cc.dpos s) (Gravity.field 1 (truePos w s) - r.cc.acc s)
        = GNC.Transported.act (r.AfC s) (r.efC w s) + r.nfC w s := by
      show _ = GNC.Transported.act (Amat (r.cc.pos s))
          (join2 (truePos w s - r.cc.pos s) (trueVel w s - r.cc.dpos s)) + r.nfC w s
      rw [act_eq, act_Amat]
      show _ = join2 (trueVel w s - r.cc.dpos s) _ + join2 (0 : E2) _
      rw [join2_add]; congr 1 <;> abel
    rw [hedot]
    have h1 : GNC.Transported.act (r.HpfC s + r.HfC s * r.AfC s) (r.efC w s)
        = GNC.Transported.act (r.HpfC s) (r.efC w s)
          + GNC.Transported.act (r.HfC s) (GNC.Transported.act (r.AfC s) (r.efC w s)) := by
      rw [GNC.Transported.act_add, GNC.Transported.act_mul]
    have h2 : GNC.Transported.act (r.HfC s) (r.nfC w s)
        = GNC.Transported.act (r.HfC s) (GNC.Transported.act (r.AfC s) (r.efC w s) + r.nfC w s)
          - GNC.Transported.act (r.HfC s) (GNC.Transported.act (r.AfC s) (r.efC w s)) := by
      rw [← map_sub]; congr 1; abel
    show GNC.Transported.act (r.HpfC s + r.HfC s * r.AfC s) (r.efC w s)
        + GNC.Transported.act (r.HfC s) (r.nfC w s) = _
    rw [h1, h2]; abel
  rw [hdrift]
  exact (act_continuous (realMat_continuous _) hce).add
    (act_continuous (realMat_continuous _)
      (join2_continuous ((trueVel_continuous hwc).sub r.cc.toCandidate.dpos_continuous)
        (hacc.sub (acc_continuous r.cc.toCandidate))))

/-- The forcing norm is bounded by the field remainder on the tube. -/
theorem nfC_bound (r : StepRecord) (hr : r.Valid) (w : ℝ → Fin 4 → ℝ) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) (r.cc.h:ℝ)) (hmem : ‖r.efC w s‖ ≤ (r.M : ℝ)) :
    ‖r.nfC w s‖ ≤ (r.KRb : ℝ) * ‖r.efC w s‖ ^ 2 + (r.Fb : ℝ) := by
  obtain ⟨hcc, _, _, hMrho, _, _, _, _, hdefFb, _, hkRcst, _⟩ := hr
  have hMrhoR : (r.M : ℝ) < (r.cc.rhoMin : ℝ) := by exact_mod_cast hMrho
  have hKRcst : (3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4) ≤ (r.KRb : ℝ) := by
    rw [← kRcst_cast r hMrho]; exact_mod_cast hkRcst
  rw [nfC, join2_left_zero_norm]
  have hqrad : (r.cc.rhoMin : ℝ) ≤ ‖r.cc.pos s‖ := r.cc.toCandidate.rhoMin_le_norm_pos hcc.1 hs
  have hposb : ‖truePos w s - r.cc.pos s‖ ≤ (r.M : ℝ) := le_trans (norm_posErr_le _ _) hmem
  have hrem := field_taylor_remainder (r.cc.pos s) (truePos w s - r.cc.pos s) hMrhoR hqrad hposb
  have hsplit : Gravity.field 1 (truePos w s) - r.cc.acc s
        - GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s)
      = (Gravity.field 1 (r.cc.pos s + (truePos w s - r.cc.pos s)) - Gravity.field 1 (r.cc.pos s)
          - GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s))
        + (Gravity.field 1 (r.cc.pos s) - r.cc.acc s) := by rw [add_sub_cancel]; abel
  have hdef : ‖Gravity.field 1 (r.cc.pos s) - r.cc.acc s‖ ≤ (r.defect : ℝ) := by
    rw [norm_sub_rev]; exact r.cc.toCandidate.defect_bound hcc.1 hs
  have hb1 : ‖Gravity.field 1 (truePos w s) - r.cc.acc s
        - GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s)‖
      ≤ (3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4) * ‖truePos w s - r.cc.pos s‖ ^ 2
        + (r.defect : ℝ) := by
    rw [hsplit]; exact (norm_add_le _ _).trans (add_le_add hrem hdef)
  have hKRnn : (0:ℝ) ≤ 3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4 := by positivity
  have hp2 : ‖truePos w s - r.cc.pos s‖ ^ 2 ≤ ‖r.efC w s‖ ^ 2 := by
    have hle := norm_posErr_le (truePos w s - r.cc.pos s) (trueVel w s - r.cc.dpos s)
    simp only [efC]
    nlinarith [hle, norm_nonneg (truePos w s - r.cc.pos s)]
  have hdefFbR : (r.defect : ℝ) ≤ (r.Fb : ℝ) := by exact_mod_cast hdefFb
  calc ‖Gravity.field 1 (truePos w s) - r.cc.acc s
          - GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s)‖
      ≤ (3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4) * ‖truePos w s - r.cc.pos s‖ ^ 2
        + (r.defect : ℝ) := hb1
    _ ≤ (r.KRb : ℝ) * ‖r.efC w s‖ ^ 2 + (r.Fb : ℝ) := by
          apply add_le_add _ hdefFbR
          calc (3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4) * ‖truePos w s - r.cc.pos s‖ ^ 2
              ≤ (3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4) * ‖r.efC w s‖ ^ 2 :=
                mul_le_mul_of_nonneg_left hp2 hKRnn
            _ ≤ (r.KRb : ℝ) * ‖r.efC w s‖ ^ 2 :=
                mul_le_mul_of_nonneg_right hKRcst (by positivity)

/-- The gradient candidate error of the step. -/
theorem gradient_defect_bound (r : StepRecord) (hr : r.Valid) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) (r.cc.h:ℝ)) :
    GNC.Transported.frob (r.AfC s - r.AhfC s) ≤ (r.cc.epsA : ℝ) := by
  show GNC.PlanarCoast.frob (Amat (r.cc.pos s) - realMat (Ahat r.cc.toCandidate) s) ≤ (r.cc.epsA : ℝ)
  rw [frob_Amat_sub_Ahat]; exact r.cc.epsA_sound hr.1 hs

/-- The residual contraction of the step at the endpoint. -/
theorem residual_end (r : StepRecord) (hr : r.Valid) :
    GNC.Transported.frob (1 - realMat r.cc.G (r.cc.h:ℝ) * realMat r.cc.H (r.cc.h:ℝ))
      ≤ (r.cc.epsI : ℝ) := by
  have hh0 : (0:ℝ) ≤ (r.cc.h:ℝ) := by exact_mod_cast hr.1.1.1
  exact r.cc.epsI_sound hr.1 (right_mem_Icc.mpr hh0)

/-- The exact step identity at the endpoint, ready to telescope through the
chain. -/
theorem step_identity_end (r : StepRecord) (hr : r.Valid) (w : ℝ → Fin 4 → ℝ)
    (hwc : Continuous w)
    (hw : ∀ s ∈ Icc (0:ℝ) (r.cc.h:ℝ), HasDerivAt w (PolynomialOrbit.physicalRate 0 (w s)) s)
    (hacc : Continuous (fun s => Gravity.field 1 (truePos w s))) :
    r.efC w (r.cc.h:ℝ)
      = GNC.Transported.act (realMat r.cc.G (r.cc.h:ℝ))
          (r.efC w 0 + ∫ s in (0:ℝ)..(r.cc.h:ℝ),
            GNC.Transported.drift r.HfC r.AfC r.HpfC (r.efC w) (r.nfC w) s)
        + GNC.Transported.act
            (1 - realMat r.cc.G (r.cc.h:ℝ) * realMat r.cc.H (r.cc.h:ℝ)) (r.efC w (r.cc.h:ℝ)) := by
  have hh0 : (0:ℝ) ≤ (r.cc.h:ℝ) := by exact_mod_cast hr.1.1.1
  refine GNC.Transported.step_identity (fun s => realMat r.cc.G s) r.HfC r.AfC r.HpfC
    (r.efC w) (r.nfC w) (r.cc.H_zero hr.1) ?hHd ?hed (r.driftC_continuous hwc hacc)
    (t := (r.cc.h:ℝ)) Set.right_mem_uIcc
  case hHd => exact fun s _ => realMat_hasDerivAt r.cc.H s
  case hed =>
    intro s hs
    rw [uIcc_of_le hh0] at hs
    exact r.efC_hasDerivAt w (hw s hs)

/-- The tube containment of the step, phrased through `efC`. -/
theorem tube_efC (r : StepRecord) (hr : r.Valid) (w : ℝ → Fin 4 → ℝ)
    (hwc : Continuous w)
    (hw : ∀ s ∈ Icc (0:ℝ) (r.cc.h:ℝ), HasDerivAt w (PolynomialOrbit.physicalRate 0 (w s)) s)
    (hacc : Continuous (fun s => Gravity.field 1 (truePos w s)))
    (hE0 : ‖r.efC w 0‖ ≤ (r.Ein : ℝ)) :
    ∀ t ∈ Icc (0:ℝ) (r.cc.h:ℝ), ‖r.efC w t‖ < (r.M : ℝ) :=
  tube_sound r hr w hwc hw hacc hE0

/-- The endpoint transition equals the stored evaluated transition, cast. -/
theorem P_eq (r : StepRecord) (hr : r.Valid) :
    realMat r.cc.G (r.cc.h : ℝ) = (r.Pev).map (Rat.cast : ℚ → ℝ) := by
  have hPev : r.Pev = evalMatQ r.cc.G r.cc.h := hr.2.2.2.2.2.2.1
  ext i j
  rw [Matrix.map_apply, hPev, evalMatQ]
  exact ev_ratEval (r.cc.G i j) r.cc.h

/-- The real evaluation of the derivative kernel `residH`. -/
theorem residH_real (r : StepRecord) (s : ℝ) :
    realMat (r.cc.residH) s = r.HpfC s + r.HfC s * r.AhfC s := by
  rw [CurvatureCandidate.residH, realMat_add, realMat_mul]; rfl

/-- The squared rational handoff jump between two consecutive candidates. -/
def jumpSq (a b : StepRecord) : ℚ :=
  (evaluate a.cc.x a.cc.h - evaluate b.cc.x 0) ^ 2
    + (evaluate a.cc.y a.cc.h - evaluate b.cc.y 0) ^ 2
    + (evaluate (differentiate a.cc.x) a.cc.h - evaluate (differentiate b.cc.x) 0) ^ 2
    + (evaluate (differentiate a.cc.y) a.cc.h - evaluate (differentiate b.cc.y) 0) ^ 2

/-- The handoff mismatch of two consecutive step error curves, sharing the true
solution across the junction, is bounded by the stored handoff radius. -/
theorem handoff_bound (a b : StepRecord) (w w' : ℝ → Fin 4 → ℝ)
    (hj : w' 0 = w (a.cc.h : ℝ)) (hcheck : jumpSq a b ≤ b.d ^ 2) (hd0 : 0 ≤ b.d) :
    ‖b.efC w' 0 - a.efC w (a.cc.h : ℝ)‖ ≤ (b.d : ℝ) := by
  have hTP : truePos w' 0 = truePos w (a.cc.h : ℝ) := by simp only [truePos, hj]
  have hTV : trueVel w' 0 = trueVel w (a.cc.h : ℝ) := by simp only [trueVel, hj]
  have hdiff : b.efC w' 0 - a.efC w (a.cc.h : ℝ)
      = join2 (a.cc.pos (a.cc.h : ℝ) - b.cc.pos 0) (a.cc.dpos (a.cc.h : ℝ) - b.cc.dpos 0) := by
    simp only [efC, join2_sub, hTP, hTV]
    congr 1 <;> abel
  have hz : (0 : ℝ) = ((0 : ℚ) : ℝ) := by norm_num
  have hnsq : ‖b.efC w' 0 - a.efC w (a.cc.h : ℝ)‖ ^ 2 = ((jumpSq a b : ℚ) : ℝ) := by
    rw [hdiff, join2_norm_sq]
    rw [Candidate.pos, Candidate.pos, pack_sub, pack_norm_sq,
      Candidate.dpos, Candidate.dpos, pack_sub, pack_norm_sq]
    rw [ev_ratEval a.cc.x a.cc.h, ev_ratEval a.cc.y a.cc.h,
      ev_ratEval (differentiate a.cc.x) a.cc.h, ev_ratEval (differentiate a.cc.y) a.cc.h,
      show (0:ℝ) = ((0:ℚ):ℝ) from hz, ev_ratEval b.cc.x 0, ev_ratEval b.cc.y 0,
      ev_ratEval (differentiate b.cc.x) 0, ev_ratEval (differentiate b.cc.y) 0]
    rw [jumpSq]; push_cast; ring
  have hd0R : (0:ℝ) ≤ (b.d : ℝ) := by exact_mod_cast hd0
  have hsq : ‖b.efC w' 0 - a.efC w (a.cc.h : ℝ)‖ ^ 2 ≤ (b.d : ℝ) ^ 2 := by
    rw [hnsq]
    calc ((jumpSq a b : ℚ) : ℝ) ≤ ((b.d ^ 2 : ℚ) : ℝ) := by exact_mod_cast hcheck
      _ = (b.d : ℝ) ^ 2 := by push_cast; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hd0R two_ne_zero).mp hsq

end StepRecord

/-! ### The composed node bound and its recurrence -/

/-- The per-step forcing constant `K_R M² + F + εA M`. -/
def forcingQ (r : StepRecord) : ℚ := r.KRb * r.M ^ 2 + r.Fb + r.cc.epsA * r.M

/-- Rational node error bound for a row set at node `i`, from the composed
transition row-restricted Frobenius bounds `kMsel`, `kSsel`, the tight per-pair
velocity-column kernel bounds `kVsel`, and the column-split initial coefficients
`kM0psel`, `kM0vsel` that transport the position and velocity initial radii
separately. The forcing term charges the tight composed kernel `kVsel`; the
derivative kernel keeps the submultiplicative `kMsel · epsH`. -/
def nodeBoundRowsQ (S : ℕ → StepRecord) (e0p e0v : ℚ)
    (kMsel kSsel kVsel : StepRecord → List ℚ) (kM0psel kM0vsel : StepRecord → ℚ) (i : ℕ) : ℚ :=
  kM0psel (S i) * e0p + kM0vsel (S i) * e0v
    + ∑ j ∈ Finset.range (i + 1),
        ((kMsel (S i)).getD j 0 * (S j).d
          + (S j).cc.h * ((kVsel (S i)).getD j 0 * forcingQ (S j)
              + (kMsel (S i)).getD j 0 * (S j).cc.epsH * (S j).M)
          + (kSsel (S i)).getD j 0 * (S j).cc.epsI * (S j).M)

/-- The full-row node error bound at node `i`. -/
abbrev nodeBoundQ (S : ℕ → StepRecord) (e0p e0v : ℚ) (i : ℕ) : ℚ :=
  nodeBoundRowsQ S e0p e0v (fun r => r.kM) (fun r => r.kS) (fun r => r.kV)
    (fun r => r.kM0p) (fun r => r.kM0v) i

/-! ### The transported chain data of a true solution -/

/-- Terminal error of step `j`. -/
def chainB (S : ℕ → StepRecord) (w : ℕ → ℝ → Fin 4 → ℝ) : ℕ → GNC.Transported.E :=
  fun j => (S j).efC (w j) ((S j).cc.h : ℝ)

/-- Handoff mismatch at the start of step `j`. -/
def chainM (S : ℕ → StepRecord) (w : ℕ → ℝ → Fin 4 → ℝ) : ℕ → GNC.Transported.E
  | 0 => 0
  | (k + 1) => (S (k + 1)).efC (w (k + 1)) 0 - (S k).efC (w k) ((S k).cc.h : ℝ)

/-- The transported drift of step `j`. -/
def chainDrift (S : ℕ → StepRecord) (w : ℕ → ℝ → Fin 4 → ℝ) (j : ℕ) : ℝ → GNC.Transported.E :=
  GNC.Transported.drift (S j).HfC (S j).AfC (S j).HpfC ((S j).efC (w j)) ((S j).nfC (w j))

/-- The step input `c j = m j + ∫ drift`. -/
def chainC (S : ℕ → StepRecord) (w : ℕ → ℝ → Fin 4 → ℝ) : ℕ → GNC.Transported.E :=
  fun j => chainM S w j + ∫ s in (0:ℝ)..((S j).cc.h : ℝ), chainDrift S w j s

/-- The residual slack `slack j = (1 - P j H_j(h_j)) (b j)`. -/
def chainSlack (S : ℕ → StepRecord) (w : ℕ → ℝ → Fin 4 → ℝ)
    (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) : ℕ → GNC.Transported.E :=
  fun j => GNC.Transported.act (1 - P j * (S j).HfC ((S j).cc.h : ℝ)) (chainB S w j)

/-- Projecting onto all rows is the identity. -/
theorem projRows_univ (v : GNC.Transported.E) : GNC.Transported.projRows Finset.univ v = v := by
  have hdiag : GNC.Transported.diagRows (Finset.univ : Finset (Fin 4)) = 1 := by
    rw [GNC.Transported.diagRows]
    ext i j; rw [Matrix.diagonal, Matrix.of_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  rw [GNC.Transported.projRows, hdiag, GNC.Transported.act_one]

theorem frobRows_univ (M : Matrix (Fin 4) (Fin 4) ℝ) :
    GNC.Transported.frobRows Finset.univ M = GNC.Transported.frob M := rfl

/-! ### The chain recurrence from the exact step identity -/

variable (S : ℕ → StepRecord) (w : ℕ → ℝ → Fin 4 → ℝ)
  (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ)

theorem chain_hc (j : ℕ) :
    chainC S w j = chainM S w j
      + ∫ s in (0:ℝ)..((S j).cc.h : ℝ),
          GNC.Transported.drift (S j).HfC (S j).AfC (S j).HpfC ((S j).efC (w j)) ((S j).nfC (w j)) s :=
  rfl

theorem chain_hslack (j : ℕ) :
    chainSlack S w P j
      = GNC.Transported.act (1 - P j * (S j).HfC ((S j).cc.h : ℝ)) (chainB S w j) := rfl

theorem chain_hbase (hP : ∀ k, P k = realMat (S k).cc.G ((S k).cc.h : ℝ))
    (hvalid : ∀ j, (S j).Valid) (hwc : ∀ j, Continuous (w j))
    (hw : ∀ j, ∀ s ∈ Icc (0:ℝ) ((S j).cc.h : ℝ),
      HasDerivAt (w j) (PolynomialOrbit.physicalRate 0 (w j s)) s)
    (hacc : ∀ j, Continuous (fun s => Gravity.field 1 (truePos (w j) s))) :
    chainB S w 0 = GNC.Transported.act (P 0) ((S 0).efC (w 0) 0 + chainC S w 0)
      + chainSlack S w P 0 := by
  have hid := (S 0).step_identity_end (hvalid 0) (w 0) (hwc 0) (hw 0) (hacc 0)
  have harg : (S 0).efC (w 0) 0 + chainC S w 0
      = (S 0).efC (w 0) 0
        + ∫ s in (0:ℝ)..((S 0).cc.h : ℝ), chainDrift S w 0 s := by
    rw [chainC, chainM]; abel
  rw [harg]
  simp only [chainB, chainSlack, chainDrift]
  rw [hP 0]
  exact hid

theorem chain_hsucc (hP : ∀ k, P k = realMat (S k).cc.G ((S k).cc.h : ℝ))
    (hvalid : ∀ j, (S j).Valid) (hwc : ∀ j, Continuous (w j))
    (hw : ∀ j, ∀ s ∈ Icc (0:ℝ) ((S j).cc.h : ℝ),
      HasDerivAt (w j) (PolynomialOrbit.physicalRate 0 (w j s)) s)
    (hacc : ∀ j, Continuous (fun s => Gravity.field 1 (truePos (w j) s))) (j : ℕ) :
    chainB S w (j + 1)
      = GNC.Transported.act (P (j + 1)) (chainB S w j + chainC S w (j + 1))
        + chainSlack S w P (j + 1) := by
  have hid := (S (j+1)).step_identity_end (hvalid (j+1)) (w (j+1)) (hwc (j+1)) (hw (j+1)) (hacc (j+1))
  have harg : chainB S w j + chainC S w (j + 1)
      = (S (j+1)).efC (w (j+1)) 0
        + ∫ s in (0:ℝ)..((S (j+1)).cc.h : ℝ), chainDrift S w (j+1) s := by
    rw [chainB, chainC, chainM]; abel
  rw [harg]
  simp only [chainB, chainSlack, chainDrift]
  rw [hP (j+1)]
  exact hid

/-- The real value of the rational node bound, in the form consumed by
`chain_bound_kernel_rows`. -/
theorem nodeBoundRowsQ_cast (S : ℕ → StepRecord) (e0p e0v : ℚ)
    (kMsel kSsel kVsel : StepRecord → List ℚ) (kM0psel kM0vsel : StepRecord → ℚ) (i : ℕ) :
    (nodeBoundRowsQ S e0p e0v kMsel kSsel kVsel kM0psel kM0vsel i : ℝ)
      = (kM0psel (S i) : ℝ) * (e0p : ℝ) + (kM0vsel (S i) : ℝ) * (e0v : ℝ)
        + ∑ j ∈ Finset.range (i + 1),
            (((kMsel (S i)).getD j 0 : ℝ) * ((S j).d : ℝ)
              + ((S j).cc.h : ℝ) * (((kVsel (S i)).getD j 0 : ℝ)
                    * (((S j).KRb : ℝ) * ((S j).M : ℝ) ^ 2 + ((S j).Fb : ℝ)
                        + ((S j).cc.epsA : ℝ) * ((S j).M : ℝ))
                  + ((kMsel (S i)).getD j 0 : ℝ) * ((S j).cc.epsH : ℝ) * ((S j).M : ℝ))
              + ((kSsel (S i)).getD j 0 : ℝ) * ((S j).cc.epsI : ℝ) * ((S j).M : ℝ)) := by
  rw [nodeBoundRowsQ]
  push_cast [forcingQ]
  rfl

/-- Bridge from a rational row-and-column-Frobenius-square check to the real
column-restricted composed transition bound consumed by `chain_terminal_bounds`
for the split initial term. -/
theorem stm_frobRowsCols_le (S : ℕ → StepRecord) (R C : Finset (Fin 4)) (i j : ℕ) (B : ℚ)
    (hnn : 0 ≤ B)
    (hsum : ∑ r ∈ R, ∑ c ∈ C, (stmQ (fun k => (S k).Pev) i j r c) ^ 2 ≤ B ^ 2) :
    GNC.Transported.frobRowsCols R C
        (GNC.Transported.stm (fun k => ((S k).Pev).map (Rat.cast : ℚ → ℝ)) i j) ≤ (B : ℝ) := by
  rw [← stmQ_cast]
  exact frobRowsCols_map_cast_le R C (stmQ (fun k => (S k).Pev) i j) hsum hnn

/-- Bridge from a rational row-Frobenius-square check to the real composed
transition bound consumed by `chain_terminal_bounds`. -/
theorem stm_frobRows_le (S : ℕ → StepRecord) (R : Finset (Fin 4)) (i j : ℕ) (B : ℚ)
    (hnn : 0 ≤ B)
    (hsum : ∑ r ∈ R, ∑ c, (stmQ (fun k => (S k).Pev) i j r c) ^ 2 ≤ B ^ 2) :
    GNC.Transported.frobRows R
        (GNC.Transported.stm (fun k => ((S k).Pev).map (Rat.cast : ℚ → ℝ)) i j) ≤ (B : ℝ) := by
  rw [← stmQ_cast]
  exact frobRows_map_cast_le R (stmQ (fun k => (S k).Pev) i j) hsum hnn

/-! ### The composed terminal error bounds of the orbit chain -/

/-- The composed curvature chain bound. For a family of valid step records with
the exported composed-transition Frobenius bounds and a true inverse-square
solution threaded through the junctions, the terminal error at the last node is
bounded by the composed node bounds for the full, position and velocity row
sets. The tube of each step is closed sequentially with `tube_sound`, and the
composed transitions carry the accumulated forcing through
`chain_bound_kernel_rows`. -/
theorem chain_terminal_bounds (S : ℕ → StepRecord) (n : ℕ) (e0p e0v : ℚ)
    (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (hP : ∀ k, P k = realMat (S k).cc.G ((S k).cc.h : ℝ))
    (hvalid : ∀ j, (S j).Valid) (w : ℕ → ℝ → Fin 4 → ℝ)
    (hwc : ∀ j, Continuous (w j))
    (hw : ∀ j, ∀ s ∈ Icc (0:ℝ) ((S j).cc.h : ℝ),
      HasDerivAt (w j) (PolynomialOrbit.physicalRate 0 (w j s)) s)
    (hacc : ∀ j, Continuous (fun s => Gravity.field 1 (truePos (w j) s)))
    (hjoin : ∀ j, j < n → w (j + 1) 0 = w j ((S j).cc.h : ℝ))
    (hinitp : ‖truePos (w 0) 0 - (S 0).cc.pos 0‖ ≤ (e0p : ℝ))
    (hinitv : ‖trueVel (w 0) 0 - (S 0).cc.dpos 0‖ ≤ (e0v : ℝ))
    (hEin0 : (S 0).Ein = e0p + e0v)
    (hEinS : ∀ j, j < n → (S (j + 1)).Ein = nodeBoundQ S e0p e0v j + (S (j + 1)).d)
    (hd0 : ∀ j, 0 ≤ (S j).d)
    (hjump : ∀ j, j < n → StepRecord.jumpSq (S j) (S (j + 1)) ≤ (S (j + 1)).d ^ 2)
    (hkMf : ∀ i, i ≤ n → ∀ j, j ≤ i →
      GNC.Transported.frobRows Finset.univ (GNC.Transported.stm P i j) ≤ ((S i).kM.getD j 0 : ℝ))
    (hkSf : ∀ i, i ≤ n → ∀ j, j ≤ i →
      GNC.Transported.frobRows Finset.univ (GNC.Transported.stm P i (j + 1)) ≤ ((S i).kS.getD j 0 : ℝ))
    (hkVf : ∀ i, i ≤ n → ∀ j, j ≤ i → ∀ s ∈ Icc (0:ℝ) ((S j).cc.h : ℝ),
      GNC.Transported.frobRowsVel Finset.univ (GNC.Transported.stm P i j * (S j).HfC s)
        ≤ ((S i).kV.getD j 0 : ℝ))
    (hkM0pf : ∀ i, i ≤ n →
      GNC.Transported.frobRowsCols Finset.univ ({0, 1} : Finset (Fin 4)) (GNC.Transported.stm P i 0)
        ≤ ((S i).kM0p : ℝ))
    (hkM0vf : ∀ i, i ≤ n →
      GNC.Transported.frobRowsCols Finset.univ ({2, 3} : Finset (Fin 4)) (GNC.Transported.stm P i 0)
        ≤ ((S i).kM0v : ℝ))
    (hkMp : ∀ j, j ≤ n →
      GNC.Transported.frobRows ({0, 1} : Finset (Fin 4)) (GNC.Transported.stm P n j)
        ≤ ((S n).kMp.getD j 0 : ℝ))
    (hkSp : ∀ j, j ≤ n →
      GNC.Transported.frobRows ({0, 1} : Finset (Fin 4)) (GNC.Transported.stm P n (j + 1))
        ≤ ((S n).kSp.getD j 0 : ℝ))
    (hkVp : ∀ j, j ≤ n → ∀ s ∈ Icc (0:ℝ) ((S j).cc.h : ℝ),
      GNC.Transported.frobRowsVel ({0, 1} : Finset (Fin 4)) (GNC.Transported.stm P n j * (S j).HfC s)
        ≤ ((S n).kVp.getD j 0 : ℝ))
    (hkM0pp :
      GNC.Transported.frobRowsCols ({0, 1} : Finset (Fin 4)) ({0, 1} : Finset (Fin 4))
        (GNC.Transported.stm P n 0) ≤ ((S n).kMp0p : ℝ))
    (hkM0vp :
      GNC.Transported.frobRowsCols ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4))
        (GNC.Transported.stm P n 0) ≤ ((S n).kMp0v : ℝ))
    (hkMv : ∀ j, j ≤ n →
      GNC.Transported.frobRows ({2, 3} : Finset (Fin 4)) (GNC.Transported.stm P n j)
        ≤ ((S n).kMv.getD j 0 : ℝ))
    (hkSv : ∀ j, j ≤ n →
      GNC.Transported.frobRows ({2, 3} : Finset (Fin 4)) (GNC.Transported.stm P n (j + 1))
        ≤ ((S n).kSv.getD j 0 : ℝ))
    (hkVv : ∀ j, j ≤ n → ∀ s ∈ Icc (0:ℝ) ((S j).cc.h : ℝ),
      GNC.Transported.frobRowsVel ({2, 3} : Finset (Fin 4)) (GNC.Transported.stm P n j * (S j).HfC s)
        ≤ ((S n).kVv.getD j 0 : ℝ))
    (hkM0pv :
      GNC.Transported.frobRowsCols ({2, 3} : Finset (Fin 4)) ({0, 1} : Finset (Fin 4))
        (GNC.Transported.stm P n 0) ≤ ((S n).kMv0p : ℝ))
    (hkM0vv :
      GNC.Transported.frobRowsCols ({2, 3} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4))
        (GNC.Transported.stm P n 0) ≤ ((S n).kMv0v : ℝ)) :
    ‖chainB S w n‖ ≤ (nodeBoundQ S e0p e0v n : ℝ)
    ∧ ‖truePos (w n) ((S n).cc.h : ℝ) - (S n).cc.pos ((S n).cc.h : ℝ)‖
        ≤ (nodeBoundRowsQ S e0p e0v (fun r => r.kMp) (fun r => r.kSp) (fun r => r.kVp)
            (fun r => r.kMp0p) (fun r => r.kMp0v) n : ℝ)
    ∧ ‖trueVel (w n) ((S n).cc.h : ℝ) - (S n).cc.dpos ((S n).cc.h : ℝ)‖
        ≤ (nodeBoundRowsQ S e0p e0v (fun r => r.kMv) (fun r => r.kSv) (fun r => r.kVv)
            (fun r => r.kMv0p) (fun r => r.kMv0v) n : ℝ) := by
  -- combined initial bound for the tube closures
  have hinit : ‖(S 0).efC (w 0) 0‖ ≤ ((e0p + e0v : ℚ) : ℝ) := by
    have he : (S 0).efC (w 0) 0
        = join2 (truePos (w 0) 0 - (S 0).cc.pos 0) (trueVel (w 0) 0 - (S 0).cc.dpos 0) := rfl
    rw [he]
    refine (join2_norm_le _ _).trans ?_
    rw [show ((e0p + e0v : ℚ) : ℝ) = (e0p : ℝ) + (e0v : ℝ) by push_cast; ring]
    exact add_le_add hinitp hinitv
  -- The composed node bound for a row set from tube containment of every step.
  have chainRows : ∀ (i : ℕ), i ≤ n → ∀ (R : Finset (Fin 4))
      (kMsel kSsel kVsel : StepRecord → List ℚ) (kM0psel kM0vsel : StepRecord → ℚ),
      (∀ j, j ≤ i → GNC.Transported.frobRows R (GNC.Transported.stm P i j)
          ≤ ((kMsel (S i)).getD j 0 : ℝ)) →
      (∀ j, j ≤ i → GNC.Transported.frobRows R (GNC.Transported.stm P i (j + 1))
          ≤ ((kSsel (S i)).getD j 0 : ℝ)) →
      (∀ j, j ≤ i → ∀ s ∈ Icc (0:ℝ) ((S j).cc.h : ℝ),
          GNC.Transported.frobRowsVel R (GNC.Transported.stm P i j * (S j).HfC s)
            ≤ ((kVsel (S i)).getD j 0 : ℝ)) →
      GNC.Transported.frobRowsCols R ({0, 1} : Finset (Fin 4)) (GNC.Transported.stm P i 0)
          ≤ (kM0psel (S i) : ℝ) →
      GNC.Transported.frobRowsCols R ({2, 3} : Finset (Fin 4)) (GNC.Transported.stm P i 0)
          ≤ (kM0vsel (S i) : ℝ) →
      (∀ j, j ≤ i → ∀ s ∈ Icc (0:ℝ) ((S j).cc.h : ℝ), ‖(S j).efC (w j) s‖ ≤ ((S j).M : ℝ)) →
      ‖GNC.Transported.projRows R (chainB S w i)‖
        ≤ (nodeBoundRowsQ S e0p e0v kMsel kSsel kVsel kM0psel kM0vsel i : ℝ) := by
    intro i _ R kMsel kSsel kVsel kM0psel kM0vsel hkM hkS hkVs hkM0p hkM0v htube
    refine le_trans (GNC.Transported.chain_bound_kernel_rows' P ((S 0).efC (w 0) 0)
      (join2 (truePos (w 0) 0 - (S 0).cc.pos 0) (0 : E2))
      (join2 (0 : E2) (trueVel (w 0) 0 - (S 0).cc.dpos 0))
      (chainB S w) (chainM S w) (chainC S w) (chainSlack S w P) R
      (fun j => (S j).HfC) (fun j => (S j).AfC) (fun j => (S j).AhfC) (fun j => (S j).HpfC)
      (fun j => (S j).efC (w j)) (fun j => (S j).nfC (w j))
      (fun j => ((S j).cc.h : ℝ))
      (fun j => ((kMsel (S i)).getD j 0 : ℝ)) (fun j => ((kSsel (S i)).getD j 0 : ℝ))
      (fun j => ((kVsel (S i)).getD j 0 : ℝ))
      (fun j => ((kMsel (S i)).getD j 0 : ℝ) * ((S j).cc.epsH : ℝ))
      (fun j => ((S j).M : ℝ)) (fun j => ((S j).Fb : ℝ)) (fun j => ((S j).KRb : ℝ))
      (fun j => ((S j).cc.epsA : ℝ)) (fun j => ((S j).cc.epsI : ℝ)) (fun j => ((S j).d : ℝ))
      (e0p : ℝ) (e0v : ℝ) (kM0psel (S i) : ℝ) (kM0vsel (S i) : ℝ)
      (chain_hbase S w P hP hvalid hwc hw hacc)
      (chain_hsucc S w P hP hvalid hwc hw hacc)
      (fun j => chain_hc S w j) (fun j => chain_hslack S w P j)
      (i := i)
      (by rw [join2_add, add_zero, zero_add]; rfl)
      (fun j hj => join2_right_zero_apply _ j hj) (fun j hj => join2_left_zero_apply _ j hj)
      hkM0p hkM0v
      (by rw [join2_right_zero_norm]; exact hinitp) (by rw [join2_left_zero_norm]; exact hinitv)
      (fun j => by show (0:ℝ) ≤ ((S j).cc.h : ℝ); exact_mod_cast (hvalid j).1.1.1)
      (fun j => (S j).driftC_continuous (hwc j) (hacc j))
      (fun j => by show (0:ℝ) ≤ ((S j).M : ℝ); exact_mod_cast (hvalid j).2.2.1)
      (fun j => by show (0:ℝ) ≤ ((S j).KRb : ℝ); exact_mod_cast (hvalid j).2.2.2.2.2.2.2.2.2.1)
      (fun j s k => (S j).AfC_sub_AhfC_row0 s k) (fun j s k => (S j).AfC_sub_AhfC_row1 s k)
      (fun j s => (S j).nfC_zero0 (w j) s) (fun j s => (S j).nfC_zero1 (w j) s)
      hkM hkS hkVs ?hkR ?hεA htube ?hnb ?hεIr ?hbtube ?hd) ?hbound
    case hkR =>
      intro j hj s hs
      have h3 : GNC.Transported.frob ((S j).HpfC s + (S j).HfC s * (S j).AhfC s)
          ≤ ((S j).cc.epsH : ℝ) := (S j).cc.epsH_sound (hvalid j).1 hs
      exact (frobRows_mul_le R _ _).trans
        (mul_le_mul (hkM j hj) h3 (GNC.Transported.frob_nonneg _)
          (le_trans (GNC.Transported.frobRows_nonneg _ _) (hkM j hj)))
    case hεA => exact fun j hj s hs => (S j).gradient_defect_bound (hvalid j) hs
    case hnb => exact fun j hj s hs hmem => (S j).nfC_bound (hvalid j) (w j) hs hmem
    case hεIr =>
      intro j hj; rw [hP j]; exact (S j).residual_end (hvalid j)
    case hbtube =>
      intro j hj
      exact htube j hj ((S j).cc.h : ℝ) (right_mem_Icc.mpr (by exact_mod_cast (hvalid j).1.1.1))
    case hd =>
      intro j hj
      match j with
      | 0 => rw [chainM, norm_zero]; show (0:ℝ) ≤ ((S 0).d : ℝ); exact_mod_cast hd0 0
      | k + 1 =>
        rw [chainM]
        exact StepRecord.handoff_bound (S k) (S (k + 1)) (w k) (w (k + 1)) (hjoin k (by omega))
          (hjump k (by omega)) (hd0 (k + 1))
    case hbound =>
      rw [nodeBoundRowsQ_cast]
      exact add_le_add (le_of_eq rfl)
        (le_of_eq (Finset.sum_congr rfl (fun j _ => by ring)))
  -- Sequential tube closure and the full node bound at every node.
  have key : ∀ i, i ≤ n → (∀ s ∈ Icc (0:ℝ) ((S i).cc.h : ℝ), ‖(S i).efC (w i) s‖ ≤ ((S i).M : ℝ))
      ∧ ‖chainB S w i‖ ≤ (nodeBoundQ S e0p e0v i : ℝ) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i IH =>
      intro hi
      -- initial-error bound of step i
      have hE0 : ‖(S i).efC (w i) 0‖ ≤ ((S i).Ein : ℝ) := by
        match i with
        | 0 => rw [hEin0]; exact hinit
        | k + 1 =>
          have hIH := (IH k (by omega) (by omega)).2
          have hm : (S (k + 1)).efC (w (k + 1)) 0
              = chainB S w k + chainM S w (k + 1) := by rw [chainM, chainB]; abel
          have hmb : ‖chainM S w (k + 1)‖ ≤ ((S (k + 1)).d : ℝ) := by
            rw [chainM]
            exact StepRecord.handoff_bound (S k) (S (k + 1)) (w k) (w (k + 1)) (hjoin k (by omega))
              (hjump k (by omega)) (hd0 (k + 1))
          rw [hEinS k (by omega)]
          calc ‖(S (k + 1)).efC (w (k + 1)) 0‖
              = ‖chainB S w k + chainM S w (k + 1)‖ := by rw [hm]
            _ ≤ ‖chainB S w k‖ + ‖chainM S w (k + 1)‖ := norm_add_le _ _
            _ ≤ (nodeBoundQ S e0p e0v k : ℝ) + ((S (k + 1)).d : ℝ) := by gcongr
            _ = ((nodeBoundQ S e0p e0v k + (S (k + 1)).d : ℚ) : ℝ) := by push_cast; ring
      -- tube of step i
      have htube_i : ∀ s ∈ Icc (0:ℝ) ((S i).cc.h : ℝ), ‖(S i).efC (w i) s‖ ≤ ((S i).M : ℝ) := by
        intro s hs
        exact le_of_lt ((S i).tube_efC (hvalid i) (w i) (hwc i) (hw i) (hacc i) hE0 s hs)
      -- tube facts for all j ≤ i
      have htube_all : ∀ j, j ≤ i → ∀ s ∈ Icc (0:ℝ) ((S j).cc.h : ℝ),
          ‖(S j).efC (w j) s‖ ≤ ((S j).M : ℝ) := by
        intro j hj
        rcases lt_or_eq_of_le hj with hlt | heq
        · exact (IH j hlt (by omega)).1
        · subst heq; exact htube_i
      refine ⟨htube_i, ?_⟩
      have hb := chainRows i hi Finset.univ (fun r => r.kM) (fun r => r.kS) (fun r => r.kV)
        (fun r => r.kM0p) (fun r => r.kM0v)
        (hkMf i hi) (hkSf i hi) (hkVf i hi) (hkM0pf i hi) (hkM0vf i hi) htube_all
      rwa [projRows_univ] at hb
  -- assemble the three terminal bounds
  have htube_all : ∀ j, j ≤ n → ∀ s ∈ Icc (0:ℝ) ((S j).cc.h : ℝ),
      ‖(S j).efC (w j) s‖ ≤ ((S j).M : ℝ) := fun j hj => (key j hj).1
  refine ⟨(key n le_rfl).2, ?_, ?_⟩
  · have hb := chainRows n le_rfl ({0, 1} : Finset (Fin 4)) (fun r => r.kMp) (fun r => r.kSp)
      (fun r => r.kVp) (fun r => r.kMp0p) (fun r => r.kMp0v)
      hkMp hkSp hkVp hkM0pp hkM0vp htube_all
    rwa [chainB, StepRecord.efC, projRows_pos, join2_right_zero_norm] at hb
  · have hb := chainRows n le_rfl ({2, 3} : Finset (Fin 4)) (fun r => r.kMv) (fun r => r.kSv)
      (fun r => r.kVv) (fun r => r.kMv0p) (fun r => r.kMv0v)
      hkMv hkSv hkVv hkM0pv hkM0vv htube_all
    rwa [chainB, StepRecord.efC, projRows_vel, join2_left_zero_norm] at hb

end GNC.Applications.CertifiedCoast.Curvature
