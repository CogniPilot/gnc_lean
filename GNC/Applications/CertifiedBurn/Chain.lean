import GNC.Applications.CertifiedBurn.Step

/-! Composition of certified burn and coast steps into node bounds of the
deviation from the first-order reachable segment. Each `BurnStep` carries the
exact endpoint evaluation `Pev_j` of its local transition candidate, whose
rational products `Φ_ij = Pev_i ⋯ Pev_j` (the rational composition `stmQ`)
transport the accumulated forcing of step `j` to node `i`. Rational pair checks
on these products certify the real hypotheses of
`GNC.Transported.chain_bound_kernel_rows'`. Sequentially closing each step tube
with `BurnStep.tube_sound`, with the handoff mismatch of the deviation bounded
by `dX + α dG`, yields at every node the full, position and velocity bounds of
the deviation, for one misalignment `δ` shared by all steps. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Finset Matrix
open GNC.Planning.PolynomialKernel GNC.PolynomialBounds
namespace GNC.Applications.CertifiedBurn
open GNC.PlanarCoast GNC.PlanarCoast.Candidate GNC.PlanarCoast.CurvatureCandidate
open GNC.PlanarBurn
open GNC.Applications.CertifiedCoast.Curvature (stmQ stmQ_cast frobRows_map_cast_le
  frobRowsCols_map_cast_le matSumSqRowsVel matSumSqRowsVel_frobRowsVel frobRows_mul_le
  join2_right_zero_norm join2_norm_le join2_right_zero_apply join2_left_zero_apply projRows_pos
  projRows_vel projRows_univ)

/-! ### The rational node bound -/

/-- The per-step forcing constant `KRb M² + Fb + εA M`. -/
def forcingQ (r : BurnStep) : ℚ := r.KRb * r.M ^ 2 + r.Fb + r.epsA * r.M

/-- Rational node bound for a row set at node `i`: the column-split initial
transport, and per step `j ≤ i` the transported handoff, the tight velocity
column kernel times the forcing, the submultiplicative derivative kernel and the
residual slack. -/
def nodeBoundRowsQ (S : ℕ → BurnStep) (e0p e0v : ℚ)
    (kMsel kSsel kVsel : BurnStep → List ℚ) (kM0psel kM0vsel : BurnStep → ℚ) (i : ℕ) : ℚ :=
  kM0psel (S i) * e0p + kM0vsel (S i) * e0v
    + ∑ j ∈ Finset.range (i + 1),
        ((kMsel (S i)).getD j 0 * (S j).d
          + (S j).bc.h * ((kVsel (S i)).getD j 0 * forcingQ (S j)
              + (kMsel (S i)).getD j 0 * (S j).epsH * (S j).M)
          + (kSsel (S i)).getD j 0 * (S j).epsI * (S j).M)

/-- The full-row node bound `E_i`. -/
abbrev nodeBoundQ (S : ℕ → BurnStep) (e0p e0v : ℚ) (i : ℕ) : ℚ :=
  nodeBoundRowsQ S e0p e0v (fun r => r.kM) (fun r => r.kS) (fun r => r.kV)
    (fun r => r.kM0p) (fun r => r.kM0v) i

/-- The position-row node bound `E^p_i`. -/
abbrev nodePosQ (S : ℕ → BurnStep) (e0p e0v : ℚ) (i : ℕ) : ℚ :=
  nodeBoundRowsQ S e0p e0v (fun r => r.kMp) (fun r => r.kSp) (fun r => r.kVp)
    (fun r => r.kMp0p) (fun r => r.kMp0v) i

/-- The velocity-row node bound `E^v_i`. -/
abbrev nodeVelQ (S : ℕ → BurnStep) (e0p e0v : ℚ) (i : ℕ) : ℚ :=
  nodeBoundRowsQ S e0p e0v (fun r => r.kMv) (fun r => r.kSv) (fun r => r.kVv)
    (fun r => r.kMv0p) (fun r => r.kMv0v) i

theorem nodeBoundRowsQ_cast (S : ℕ → BurnStep) (e0p e0v : ℚ)
    (kMsel kSsel kVsel : BurnStep → List ℚ) (kM0psel kM0vsel : BurnStep → ℚ) (i : ℕ) :
    (nodeBoundRowsQ S e0p e0v kMsel kSsel kVsel kM0psel kM0vsel i : ℝ)
      = (kM0psel (S i) : ℝ) * (e0p : ℝ) + (kM0vsel (S i) : ℝ) * (e0v : ℝ)
        + ∑ j ∈ Finset.range (i + 1),
            (((kMsel (S i)).getD j 0 : ℝ) * ((S j).d : ℝ)
              + ((S j).bc.h : ℝ) * (((kVsel (S i)).getD j 0 : ℝ)
                    * (((S j).KRb : ℝ) * ((S j).M : ℝ) ^ 2 + ((S j).Fb : ℝ)
                        + ((S j).epsA : ℝ) * ((S j).M : ℝ))
                  + ((kMsel (S i)).getD j 0 : ℝ) * ((S j).epsH : ℝ) * ((S j).M : ℝ))
              + ((kSsel (S i)).getD j 0 : ℝ) * ((S j).epsI : ℝ) * ((S j).M : ℝ)) := by
  rw [nodeBoundRowsQ]
  push_cast [forcingQ]
  rfl

/-! ### Rational pair checks of the composed transitions -/

/-- The evaluated local transitions of a chain. -/
def Pq (S : ℕ → BurnStep) (k : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := (S k).Pev

/-- Row-restricted Frobenius-square checks of `Φ i j` and `Φ i (j+1)` for all
`j ≤ i`. -/
def pairChecksM (S : ℕ → BurnStep) (R : Finset (Fin 4)) (kMsel kSsel : BurnStep → List ℚ)
    (i : ℕ) : Prop :=
  ∀ j ∈ Finset.range (i + 1),
    0 ≤ (kMsel (S i)).getD j 0
    ∧ (∑ r ∈ R, ∑ c, (stmQ (Pq S) i j r c) ^ 2) ≤ ((kMsel (S i)).getD j 0) ^ 2
    ∧ 0 ≤ (kSsel (S i)).getD j 0
    ∧ (∑ r ∈ R, ∑ c, (stmQ (Pq S) i (j + 1) r c) ^ 2) ≤ ((kSsel (S i)).getD j 0) ^ 2

instance (S : ℕ → BurnStep) (R : Finset (Fin 4)) (kMsel kSsel : BurnStep → List ℚ) (i : ℕ) :
    Decidable (pairChecksM S R kMsel kSsel i) := by unfold pairChecksM; infer_instance

/-- Tight velocity-column kernel checks: the polynomial product `Φ i j · H_j`
on the rows `R` and the velocity columns is bounded by `kV_ij` on step `j`. -/
def pairChecksV (S : ℕ → BurnStep) (R : Finset (Fin 4)) (kVsel : BurnStep → List ℚ)
    (i : ℕ) : Prop :=
  ∀ j ∈ Finset.range (i + 1),
    0 ≤ (kVsel (S i)).getD j 0
    ∧ matSumSqRowsVel (cMul (stmQ (Pq S) i j) (S j).cc.H) (S j).bc.h R
        ≤ ((kVsel (S i)).getD j 0) ^ 2

instance (S : ℕ → BurnStep) (R : Finset (Fin 4)) (kVsel : BurnStep → List ℚ) (i : ℕ) :
    Decidable (pairChecksV S R kVsel i) := by unfold pairChecksV; infer_instance

/-- Column-split checks of the initial composed transition `Φ i 0`. -/
def initChecks (S : ℕ → BurnStep) (R : Finset (Fin 4)) (kM0psel kM0vsel : BurnStep → ℚ)
    (i : ℕ) : Prop :=
  0 ≤ kM0psel (S i)
  ∧ (∑ r ∈ R, ∑ c ∈ ({0, 1} : Finset (Fin 4)), (stmQ (Pq S) i 0 r c) ^ 2) ≤ (kM0psel (S i)) ^ 2
  ∧ 0 ≤ kM0vsel (S i)
  ∧ (∑ r ∈ R, ∑ c ∈ ({2, 3} : Finset (Fin 4)), (stmQ (Pq S) i 0 r c) ^ 2) ≤ (kM0vsel (S i)) ^ 2

instance (S : ℕ → BurnStep) (R : Finset (Fin 4)) (kM0psel kM0vsel : BurnStep → ℚ) (i : ℕ) :
    Decidable (initChecks S R kM0psel kM0vsel i) := by unfold initChecks; infer_instance

/-- The real composed transitions of a chain. -/
def Pr (S : ℕ → BurnStep) (k : ℕ) : Matrix (Fin 4) (Fin 4) ℝ := ((S k).Pev).map (Rat.cast : ℚ → ℝ)

theorem stm_cast (S : ℕ → BurnStep) (i j : ℕ) :
    GNC.Transported.stm (Pr S) i j = (stmQ (Pq S) i j).map (Rat.cast : ℚ → ℝ) :=
  (stmQ_cast (Pq S) i j).symm

theorem pairChecksM_real {S : ℕ → BurnStep} {R : Finset (Fin 4)} {kMsel kSsel : BurnStep → List ℚ}
    {i : ℕ} (h : pairChecksM S R kMsel kSsel i) :
    (∀ j, j ≤ i → GNC.Transported.frobRows R (GNC.Transported.stm (Pr S) i j)
        ≤ ((kMsel (S i)).getD j 0 : ℝ))
    ∧ (∀ j, j ≤ i → GNC.Transported.frobRows R (GNC.Transported.stm (Pr S) i (j + 1))
        ≤ ((kSsel (S i)).getD j 0 : ℝ)) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have hp := h j (Finset.mem_range.mpr (by omega))
    rw [stm_cast]; exact frobRows_map_cast_le R _ hp.2.1 hp.1
  · have hp := h j (Finset.mem_range.mpr (by omega))
    rw [stm_cast]; exact frobRows_map_cast_le R _ hp.2.2.2 hp.2.2.1

theorem pairChecksV_real {S : ℕ → BurnStep} {R : Finset (Fin 4)} {kVsel : BurnStep → List ℚ}
    {i : ℕ} (h : pairChecksV S R kVsel i) :
    ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) ((S j).bc.h : ℝ),
      GNC.Transported.frobRowsVel R (GNC.Transported.stm (Pr S) i j * (S j).HfC s)
        ≤ ((kVsel (S i)).getD j 0 : ℝ) := by
  intro j hj s hs
  have hp := h j (Finset.mem_range.mpr (by omega))
  have habs : |s| ≤ ((S j).bc.h : ℝ) := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hb := matSumSqRowsVel_frobRowsVel (cMul (stmQ (Pq S) i j) (S j).cc.H) habs R _ hp.2 hp.1
  rw [realMat_cMul] at hb
  have hcast : (⇑(Rat.castHom ℝ) : ℚ → ℝ) = (Rat.cast : ℚ → ℝ) := rfl
  rw [hcast] at hb
  rw [stm_cast]; exact hb

theorem initChecks_real {S : ℕ → BurnStep} {R : Finset (Fin 4)} {kM0psel kM0vsel : BurnStep → ℚ}
    {i : ℕ} (h : initChecks S R kM0psel kM0vsel i) :
    GNC.Transported.frobRowsCols R ({0, 1} : Finset (Fin 4)) (GNC.Transported.stm (Pr S) i 0)
        ≤ (kM0psel (S i) : ℝ)
    ∧ GNC.Transported.frobRowsCols R ({2, 3} : Finset (Fin 4)) (GNC.Transported.stm (Pr S) i 0)
        ≤ (kM0vsel (S i) : ℝ) := by
  rw [stm_cast]
  exact ⟨frobRowsCols_map_cast_le R _ _ h.2.1 h.1, frobRowsCols_map_cast_le R _ _ h.2.2.2 h.2.2.1⟩

/-! ### The transported chain data of a true motion -/

section Data
variable (S : ℕ → BurnStep) (Q V : ℕ → ℝ → E2) (δ : ℝ)

/-- Terminal deviation of step `j`. -/
def chainB : ℕ → GNC.Transported.E :=
  fun j => (S j).efC (Q j) (V j) δ ((S j).bc.h : ℝ)

/-- Handoff mismatch of the deviation at the start of step `j`. -/
def chainM : ℕ → GNC.Transported.E
  | 0 => 0
  | (k + 1) => (S (k + 1)).efC (Q (k + 1)) (V (k + 1)) δ 0 - (S k).efC (Q k) (V k) δ ((S k).bc.h : ℝ)

/-- The transported drift of step `j`. -/
def chainDrift (j : ℕ) : ℝ → GNC.Transported.E :=
  GNC.Transported.drift (S j).HfC (S j).AfC (S j).HpfC ((S j).efC (Q j) (V j) δ)
    ((S j).nfC (Q j) (V j) δ)

/-- The step input `c j = m j + ∫ drift`. -/
def chainC : ℕ → GNC.Transported.E :=
  fun j => chainM S Q V δ j + ∫ s in (0 : ℝ)..((S j).bc.h : ℝ), chainDrift S Q V δ j s

/-- The residual slack `(1 - P j H_j(h_j)) (b j)`. -/
def chainSlack : ℕ → GNC.Transported.E :=
  fun j => GNC.Transported.act (1 - Pr S j * (S j).HfC ((S j).bc.h : ℝ)) (chainB S Q V δ j)

end Data

/-! ### The chain node bounds -/

/-- The certified node bounds of the burn chain. For valid records, a
misalignment `|δ| ≤ α_j` shared by all steps, a true motion `(Q j, V j)` per step
that is continuous across the junctions, an initial deviation within the radii
`e0p`, `e0v`, the node inputs `Ein` recorded as the previous full node bound plus
the handoff radius, and the rational pair checks at every node `i ≤ n`, the
deviation at the end of every step `i ≤ n` satisfies the full, position and
velocity node bounds. -/
theorem chain_node_bounds (S : ℕ → BurnStep) (n : ℕ) (e0p e0v : ℚ)
    (hvalid : ∀ j, (S j).Valid) (Q V : ℕ → ℝ → E2) (δ : ℝ)
    (hδ : ∀ j, |δ| ≤ ((S j).bc.alpha : ℝ))
    (hQc : ∀ j, Continuous (Q j)) (hVc : ∀ j, Continuous (V j))
    (hfc : ∀ j, Continuous (fun s => Gravity.field 1 (Q j s)))
    (hQ : ∀ j, ∀ s ∈ Icc (0 : ℝ) ((S j).bc.h : ℝ), HasDerivAt (Q j) (V j s) s)
    (hV : ∀ j, ∀ s ∈ Icc (0 : ℝ) ((S j).bc.h : ℝ),
      HasDerivAt (V j) (Gravity.field 1 (Q j s) + (S j).bc.thrustAcc δ s) s)
    (hjQ : ∀ j, j < n → Q (j + 1) 0 = Q j ((S j).bc.h : ℝ))
    (hjV : ∀ j, j < n → V (j + 1) 0 = V j ((S j).bc.h : ℝ))
    (hinitp : ‖Q 0 0 - (S 0).bc.toCandidate.pos 0 - δ • (S 0).bc.gp 0‖ ≤ (e0p : ℝ))
    (hinitv : ‖V 0 0 - (S 0).bc.toCandidate.dpos 0 - δ • (S 0).bc.gv 0‖ ≤ (e0v : ℝ))
    (hEin0 : (S 0).Ein = e0p + e0v)
    (hEinS : ∀ j, j < n → (S (j + 1)).Ein = nodeBoundQ S e0p e0v j + (S (j + 1)).d)
    (hjX : ∀ j, j < n → BurnStep.jumpSqX (S j) (S (j + 1)) ≤ (S (j + 1)).dX ^ 2)
    (hjG : ∀ j, j < n → BurnStep.jumpSqG (S j) (S (j + 1)) ≤ (S (j + 1)).dG ^ 2)
    (hMf : ∀ i, i ≤ n → pairChecksM S Finset.univ (fun r => r.kM) (fun r => r.kS) i)
    (hVf : ∀ i, i ≤ n → pairChecksV S Finset.univ (fun r => r.kV) i)
    (hIf : ∀ i, i ≤ n → initChecks S Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) i)
    (hMp : ∀ i, i ≤ n → pairChecksM S {0, 1} (fun r => r.kMp) (fun r => r.kSp) i)
    (hVp : ∀ i, i ≤ n → pairChecksV S {0, 1} (fun r => r.kVp) i)
    (hIp : ∀ i, i ≤ n → initChecks S {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) i)
    (hMv : ∀ i, i ≤ n → pairChecksM S {2, 3} (fun r => r.kMv) (fun r => r.kSv) i)
    (hVv : ∀ i, i ≤ n → pairChecksV S {2, 3} (fun r => r.kVv) i)
    (hIv : ∀ i, i ≤ n → initChecks S {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) i) :
    ∀ i, i ≤ n →
      ‖chainB S Q V δ i‖ ≤ (nodeBoundQ S e0p e0v i : ℝ)
      ∧ ‖Q i ((S i).bc.h : ℝ) - (S i).bc.toCandidate.pos ((S i).bc.h : ℝ)
            - δ • (S i).bc.gp ((S i).bc.h : ℝ)‖ ≤ (nodePosQ S e0p e0v i : ℝ)
      ∧ ‖V i ((S i).bc.h : ℝ) - (S i).bc.toCandidate.dpos ((S i).bc.h : ℝ)
            - δ • (S i).bc.gv ((S i).bc.h : ℝ)‖ ≤ (nodeVelQ S e0p e0v i : ℝ) := by
  have hP : ∀ k, Pr S k = realMat (S k).G ((S k).bc.h : ℝ) :=
    fun k => ((S k).P_eq (hvalid k)).symm
  -- the handoff mismatch
  have hmis : ∀ k, k < n → ‖chainM S Q V δ (k + 1)‖ ≤ ((S (k + 1)).d : ℝ) := by
    intro k hk
    rw [chainM]
    exact BurnStep.handoff (S k) (S (k + 1)) (hvalid (k + 1)) (hδ (k + 1)) (hjQ k hk) (hjV k hk)
      (hjX k hk) (hjG k hk)
  have hd0 : ∀ j, (0 : ℝ) ≤ ((S j).d : ℝ) := by
    intro j
    obtain ⟨hbc, _, _, _, _, _, _, _, hdX, hdG, hd, _⟩ := hvalid j
    have hα : 0 ≤ (S j).bc.alpha := hbc.2.2.2.2.2.1
    have : 0 ≤ (S j).d := by rw [hd]; exact add_nonneg hdX (mul_nonneg hα hdG)
    exact_mod_cast this
  -- the transported step identities
  have hbase : chainB S Q V δ 0
      = GNC.Transported.act (Pr S 0) ((S 0).efC (Q 0) (V 0) δ 0 + chainC S Q V δ 0)
        + chainSlack S Q V δ 0 := by
    have hid := (S 0).step_identity_end (hvalid 0) δ (hQc 0) (hVc 0) (hfc 0) (hQ 0) (hV 0)
    have harg : (S 0).efC (Q 0) (V 0) δ 0 + chainC S Q V δ 0
        = (S 0).efC (Q 0) (V 0) δ 0
          + ∫ s in (0 : ℝ)..((S 0).bc.h : ℝ), chainDrift S Q V δ 0 s := by
      rw [chainC, chainM]; abel
    rw [harg]
    simp only [chainB, chainSlack, chainDrift]
    rw [hP 0]
    exact hid
  have hsucc : ∀ j, chainB S Q V δ (j + 1)
      = GNC.Transported.act (Pr S (j + 1)) (chainB S Q V δ j + chainC S Q V δ (j + 1))
        + chainSlack S Q V δ (j + 1) := by
    intro j
    have hid := (S (j + 1)).step_identity_end (hvalid (j + 1)) δ (hQc (j + 1)) (hVc (j + 1))
      (hfc (j + 1)) (hQ (j + 1)) (hV (j + 1))
    have harg : chainB S Q V δ j + chainC S Q V δ (j + 1)
        = (S (j + 1)).efC (Q (j + 1)) (V (j + 1)) δ 0
          + ∫ s in (0 : ℝ)..((S (j + 1)).bc.h : ℝ), chainDrift S Q V δ (j + 1) s := by
      rw [chainB, chainC, chainM]; abel
    rw [harg]
    simp only [chainB, chainSlack, chainDrift]
    rw [hP (j + 1)]
    exact hid
  have hinit : ‖(S 0).efC (Q 0) (V 0) δ 0‖ ≤ ((e0p + e0v : ℚ) : ℝ) := by
    show ‖join2 _ _‖ ≤ _
    refine (join2_norm_le _ _).trans ?_
    rw [show ((e0p + e0v : ℚ) : ℝ) = (e0p : ℝ) + (e0v : ℝ) by push_cast; ring]
    exact add_le_add hinitp hinitv
  -- the composed node bound for a row set, from tube containment of every step
  have chainRows : ∀ (i : ℕ), ∀ (R : Finset (Fin 4))
      (kMsel kSsel kVsel : BurnStep → List ℚ) (kM0psel kM0vsel : BurnStep → ℚ),
      pairChecksM S R kMsel kSsel i → pairChecksV S R kVsel i →
      initChecks S R kM0psel kM0vsel i →
      (∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) ((S j).bc.h : ℝ),
          ‖(S j).efC (Q j) (V j) δ s‖ ≤ ((S j).M : ℝ)) →
      (∀ j, j ≤ i → ‖chainM S Q V δ j‖ ≤ ((S j).d : ℝ)) →
      ‖GNC.Transported.projRows R (chainB S Q V δ i)‖
        ≤ (nodeBoundRowsQ S e0p e0v kMsel kSsel kVsel kM0psel kM0vsel i : ℝ) := by
    intro i R kMsel kSsel kVsel kM0psel kM0vsel hM hV' hI htube hmj
    obtain ⟨hkM, hkS⟩ := pairChecksM_real hM
    have hkV := pairChecksV_real hV'
    obtain ⟨hkM0p, hkM0v⟩ := initChecks_real hI
    refine le_trans (GNC.Transported.chain_bound_kernel_rows' (Pr S) ((S 0).efC (Q 0) (V 0) δ 0)
      (join2 (Q 0 0 - (S 0).bc.toCandidate.pos 0 - δ • (S 0).bc.gp 0) (0 : E2))
      (join2 (0 : E2) (V 0 0 - (S 0).bc.toCandidate.dpos 0 - δ • (S 0).bc.gv 0))
      (chainB S Q V δ) (chainM S Q V δ) (chainC S Q V δ) (chainSlack S Q V δ) R
      (fun j => (S j).HfC) (fun j => (S j).AfC) (fun j => (S j).AhfC) (fun j => (S j).HpfC)
      (fun j => (S j).efC (Q j) (V j) δ) (fun j => (S j).nfC (Q j) (V j) δ)
      (fun j => ((S j).bc.h : ℝ))
      (fun j => ((kMsel (S i)).getD j 0 : ℝ)) (fun j => ((kSsel (S i)).getD j 0 : ℝ))
      (fun j => ((kVsel (S i)).getD j 0 : ℝ))
      (fun j => ((kMsel (S i)).getD j 0 : ℝ) * ((S j).epsH : ℝ))
      (fun j => ((S j).M : ℝ)) (fun j => ((S j).Fb : ℝ)) (fun j => ((S j).KRb : ℝ))
      (fun j => ((S j).epsA : ℝ)) (fun j => ((S j).epsI : ℝ)) (fun j => ((S j).d : ℝ))
      (e0p : ℝ) (e0v : ℝ) (kM0psel (S i) : ℝ) (kM0vsel (S i) : ℝ)
      hbase hsucc (fun j => rfl) (fun j => rfl)
      (i := i)
      (by rw [join2_add, add_zero, zero_add]; rfl)
      (fun j hj => join2_right_zero_apply _ j hj) (fun j hj => join2_left_zero_apply _ j hj)
      hkM0p hkM0v
      (by rw [join2_right_zero_norm]; exact hinitp) (by rw [join2_left_zero_norm]; exact hinitv)
      (fun j => by show (0 : ℝ) ≤ ((S j).bc.h : ℝ); exact_mod_cast (hvalid j).1.1.1)
      (fun j => (S j).driftC_continuous (hvalid j).1 δ (hQc j) (hVc j) (hfc j))
      (fun j => by show (0 : ℝ) ≤ ((S j).M : ℝ); exact_mod_cast (hvalid j).2.2.2.1)
      (fun j => by
        show (0 : ℝ) ≤ ((S j).KRb : ℝ); exact_mod_cast (hvalid j).2.2.2.2.2.2.2.2.2.2.2.1)
      (fun j s k => (S j).AfC_sub_AhfC_row0 s k) (fun j s k => (S j).AfC_sub_AhfC_row1 s k)
      (fun j s => (S j).nfC_zero0 (Q j) (V j) δ s) (fun j s => (S j).nfC_zero1 (Q j) (V j) δ s)
      hkM hkS hkV ?hkR ?hεA htube ?hnb ?hεIr ?hbtube hmj) ?hbound
    case hkR =>
      intro j hj s hs
      have h3 : GNC.Transported.frob ((S j).HpfC s + (S j).HfC s * (S j).AhfC s)
          ≤ ((S j).epsH : ℝ) := (S j).cc.epsH_sound (hvalid j).2.1 hs
      exact (frobRows_mul_le R _ _).trans
        (mul_le_mul (hkM j hj) h3 (GNC.Transported.frob_nonneg _)
          (le_trans (GNC.Transported.frobRows_nonneg _ _) (hkM j hj)))
    case hεA => exact fun j hj s hs => (S j).gradient_defect_bound (hvalid j) hs
    case hnb =>
      exact fun j hj s hs hmem =>
        (S j).nfC_bound (hvalid j) (hδ j) hs (hQ j s hs) (hV j s hs) hmem
    case hεIr =>
      intro j hj; rw [hP j]; exact (S j).residual_end (hvalid j)
    case hbtube =>
      intro j hj
      exact htube j hj ((S j).bc.h : ℝ) (right_mem_Icc.mpr (by exact_mod_cast (hvalid j).1.1.1))
    case hbound =>
      rw [nodeBoundRowsQ_cast]
      exact add_le_add (le_of_eq rfl)
        (le_of_eq (Finset.sum_congr rfl (fun j _ => by ring)))
  -- mismatch bounds at every node up to n
  have hmj : ∀ i, i ≤ n → ∀ j, j ≤ i → ‖chainM S Q V δ j‖ ≤ ((S j).d : ℝ) := by
    intro i hi j hj
    match j with
    | 0 => rw [chainM, norm_zero]; exact hd0 0
    | k + 1 => exact hmis k (by omega)
  -- sequential tube closure and the full node bound at every node
  have key : ∀ i, i ≤ n →
      (∀ s ∈ Icc (0 : ℝ) ((S i).bc.h : ℝ), ‖(S i).efC (Q i) (V i) δ s‖ ≤ ((S i).M : ℝ))
      ∧ ‖chainB S Q V δ i‖ ≤ (nodeBoundQ S e0p e0v i : ℝ) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i IH =>
      intro hi
      have hE0 : ‖(S i).efC (Q i) (V i) δ 0‖ ≤ ((S i).Ein : ℝ) := by
        match i with
        | 0 => rw [hEin0]; exact hinit
        | k + 1 =>
          have hIH := (IH k (by omega) (by omega)).2
          have hm : (S (k + 1)).efC (Q (k + 1)) (V (k + 1)) δ 0
              = chainB S Q V δ k + chainM S Q V δ (k + 1) := by rw [chainM, chainB]; abel
          rw [hEinS k (by omega)]
          calc ‖(S (k + 1)).efC (Q (k + 1)) (V (k + 1)) δ 0‖
              = ‖chainB S Q V δ k + chainM S Q V δ (k + 1)‖ := by rw [hm]
            _ ≤ ‖chainB S Q V δ k‖ + ‖chainM S Q V δ (k + 1)‖ := norm_add_le _ _
            _ ≤ (nodeBoundQ S e0p e0v k : ℝ) + ((S (k + 1)).d : ℝ) :=
                add_le_add hIH (hmis k (by omega))
            _ = ((nodeBoundQ S e0p e0v k + (S (k + 1)).d : ℚ) : ℝ) := by push_cast; ring
      have htube_i : ∀ s ∈ Icc (0 : ℝ) ((S i).bc.h : ℝ),
          ‖(S i).efC (Q i) (V i) δ s‖ ≤ ((S i).M : ℝ) := by
        intro s hs
        exact le_of_lt ((S i).tube_sound (hvalid i) (hδ i) (hQc i) (hVc i) (hfc i) (hQ i) (hV i)
          hE0 s hs)
      have htube_all : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) ((S j).bc.h : ℝ),
          ‖(S j).efC (Q j) (V j) δ s‖ ≤ ((S j).M : ℝ) := by
        intro j hj
        rcases lt_or_eq_of_le hj with hlt | heq
        · exact (IH j hlt (by omega)).1
        · subst heq; exact htube_i
      refine ⟨htube_i, ?_⟩
      have hb := chainRows i Finset.univ (fun r => r.kM) (fun r => r.kS) (fun r => r.kV)
        (fun r => r.kM0p) (fun r => r.kM0v) (hMf i hi) (hVf i hi) (hIf i hi) htube_all
        (hmj i hi)
      rwa [projRows_univ] at hb
  intro i hi
  have htube_all : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) ((S j).bc.h : ℝ),
      ‖(S j).efC (Q j) (V j) δ s‖ ≤ ((S j).M : ℝ) := fun j hj => (key j (by omega)).1
  refine ⟨(key i hi).2, ?_, ?_⟩
  · have hb := chainRows i ({0, 1} : Finset (Fin 4)) (fun r => r.kMp) (fun r => r.kSp)
      (fun r => r.kVp) (fun r => r.kMp0p) (fun r => r.kMp0v) (hMp i hi) (hVp i hi) (hIp i hi)
      htube_all (hmj i hi)
    rwa [chainB, BurnStep.efC, BurnCandidate.dev, projRows_pos, join2_right_zero_norm] at hb
  · have hb := chainRows i ({2, 3} : Finset (Fin 4)) (fun r => r.kMv) (fun r => r.kSv)
      (fun r => r.kVv) (fun r => r.kMv0p) (fun r => r.kMv0v) (hMv i hi) (hVv i hi) (hIv i hi)
      htube_all (hmj i hi)
    rwa [chainB, BurnStep.efC, BurnCandidate.dev, projRows_vel, join2_left_zero_norm] at hb

end GNC.Applications.CertifiedBurn
