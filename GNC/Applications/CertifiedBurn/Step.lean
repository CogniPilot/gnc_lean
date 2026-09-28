import GNC.Applications.CertifiedCoast.Curvature.Chain
import GNC.Dynamics.PlanarBurnDefect

/-! One certified step of the burn reachable-set certificate. A `BurnStep`
bundles a `BurnCandidate` (the state, reciprocal-mass and misalignment
sensitivity polynomials of one step) with the transition candidate `G` and its
rational residuals, which together form the `CurvatureCandidate` `cc` on the
same position candidate. On top of these it stores the handoff bounds `dX`, `dG`
of the nominal and sensitivity jumps at the step start and their combination
`d = dX + α dG`, the tube radius `M`, the node input `Ein`, small-denominator
upper bounds `Fb` of the burn forcing constant and `KRb` of the remainder
constant `3 / (ρmin - M - α Gp)⁴`, the exact endpoint evaluation `Pev` of the
transition candidate, and the pair bounds of the composed transitions consumed
by the chain.

The deviation `e = (q - q̂ - δ ĝ_p, q' - q̂' - δ ĝ_v)` of a true motion obeys the
transported linear dynamics of `error_dynamics_burn`, so the first exit tube
`GNC.Transported.step_tube` applies with the transition candidate `Ψ = G`, its
symplectic partner `H`, and the polynomial gradient candidate `Â`, uniformly
for burn steps and for coast steps (`f = 0`). The forcing curve uses the thrust
at the time clamped to `[0, h]`, which agrees with the physical thrust on the
step and is continuous on the whole line. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Finset Matrix
open GNC.Planning.PolynomialKernel GNC.PolynomialBounds
namespace GNC.Applications.CertifiedBurn
open GNC.PlanarCoast GNC.PlanarCoast.Candidate GNC.PlanarCoast.CurvatureCandidate
open GNC.PlanarBurn
open GNC.Applications.CertifiedCoast.Curvature (evalMatQ realMat_hasDerivAt realMat_continuous
  frobVel_velCols act_eq act_continuous join2_continuous pack_continuous acc_continuous join2_sub
  Amat_sub_Ahat_row0 Amat_sub_Ahat_row1 frob_Amat_sub_Ahat ev_ratEval)

/-! ### Time clamping -/

/-- The time clamped to `[0, h]`. -/
def clampT (h s : ℝ) : ℝ := max 0 (min s h)

theorem clampT_of_mem {h s : ℝ} (hs : s ∈ Icc (0 : ℝ) h) : clampT h s = s := by
  unfold clampT; rw [min_eq_left hs.2, max_eq_right hs.1]

theorem clampT_mem {h : ℝ} (hh : 0 ≤ h) (s : ℝ) : clampT h s ∈ Icc (0 : ℝ) h :=
  ⟨le_max_left _ _, max_le hh (min_le_right _ _)⟩

theorem clampT_continuous (h : ℝ) : Continuous (clampT h) :=
  continuous_const.max (continuous_id.min continuous_const)

/-! ### The certified burn step record -/

/-- One step of the burn reachable-set certificate. -/
structure BurnStep where
  /-- State, reciprocal-mass and sensitivity candidate of the step. -/
  bc : BurnCandidate
  /-- The 16 polynomial entries of the local transition candidate `Ψ`. -/
  G : PolyMat
  /-- Bound of `sup ‖1 - Ψ H‖`. -/
  epsI : ℚ
  /-- Bound of `sup ‖H' + H Â‖`. -/
  epsH : ℚ
  /-- Bound of `sup ‖Ψ‖`. -/
  gSup : ℚ
  /-- Bound of `sup ‖H‖`. -/
  hSup : ℚ
  /-- Bound of `sup ‖H‖` on the velocity columns. -/
  kVloc : ℚ
  /-- Small-denominator bound of the gradient candidate error. -/
  epsA : ℚ
  /-- Bound on the jump of the nominal candidate at the step start. -/
  dX : ℚ
  /-- Bound on the jump of the sensitivity candidate at the step start. -/
  dG : ℚ
  /-- Bound on the handoff mismatch of the deviation, `dX + α dG`. -/
  d : ℚ
  /-- Tube radius of the step. -/
  M : ℚ
  /-- Bound on the initial deviation of the step. -/
  Ein : ℚ
  /-- Small-denominator upper bound of the burn forcing constant `Ftot`. -/
  Fb : ℚ
  /-- Small-denominator upper bound of `3 / (ρmin - M - α Gp)⁴`. -/
  KRb : ℚ
  /-- Exact rational evaluation of the transition candidate at the endpoint. -/
  Pev : Matrix (Fin 4) (Fin 4) ℚ
  /-- Full-row bounds `frob (Φ i j)`, indexed by `j`. -/
  kM : List ℚ
  /-- Full-row slack bounds `frob (Φ i (j+1))`. -/
  kS : List ℚ
  /-- Full-row velocity-column kernel bounds `frobVel (Φ i j * H j)`. -/
  kV : List ℚ
  /-- Full-row derivative kernel bounds `frob (Φ i j) * epsH j`. -/
  kR : List ℚ
  /-- Position-row bounds. -/
  kMp : List ℚ
  kSp : List ℚ
  kVp : List ℚ
  kRp : List ℚ
  /-- Velocity-row bounds. -/
  kMv : List ℚ
  kSv : List ℚ
  kVv : List ℚ
  kRv : List ℚ
  /-- Column-split bounds of the initial composed transition `Φ i 0`
  (position columns `0, 1` and velocity columns `2, 3`) for the full, position
  and velocity row sets. -/
  kM0p : ℚ
  kM0v : ℚ
  kMp0p : ℚ
  kMp0v : ℚ
  kMv0p : ℚ
  kMv0v : ℚ

namespace BurnStep

/-- The curvature candidate on the same position candidate as the burn step. -/
def cc (r : BurnStep) : CurvatureCandidate :=
  { toCandidate := r.bc.toCandidate, G := r.G, epsI := r.epsI, epsH := r.epsH,
    gSup := r.gSup, hSup := r.hSup, kV := r.kVloc, epsA := r.epsA, Mtube := r.M }

/-- The remainder constant of `error_dynamics_burn` on the tube. -/
def kRcst (r : BurnStep) : ℚ := 3 / (r.bc.rhoMin - r.M - r.bc.alpha * r.bc.Gp) ^ 4

/-- The burn forcing constant `Ftot` with the remainder constant replaced by
its bound `KRb`. -/
def FtotB (r : BurnStep) : ℚ :=
  r.bc.Fx + r.bc.alpha * r.bc.Fg + r.bc.Fmis + r.KRb * r.bc.alpha ^ 2 * r.bc.Gp ^ 2
    + 2 * r.KRb * r.bc.alpha * r.bc.Gp * r.M

/-- The decidable rational hypotheses of one certified step: the burn and
curvature certificates, the residual contraction, the tube geometry
`M + α Gp < ρmin`, the endpoint evaluation, the handoff combination, the
soundness of the small bounds `KRb`, `Fb`, and the first exit tube closure. -/
def Valid (r : BurnStep) : Prop :=
  r.bc.Valid ∧ r.cc.Valid ∧ r.epsI < 1 ∧ 0 ≤ r.M ∧
  r.M + r.bc.alpha * r.bc.Gp < r.bc.rhoMin ∧ 0 ≤ r.Ein ∧ r.Ein < r.M ∧
  r.Pev = evalMatQ r.G r.bc.h ∧ 0 ≤ r.dX ∧ 0 ≤ r.dG ∧ r.d = r.dX + r.bc.alpha * r.dG ∧
  0 ≤ r.KRb ∧ r.kRcst ≤ r.KRb ∧ 0 ≤ r.Fb ∧ r.FtotB ≤ r.Fb ∧
  r.gSup * (r.Ein + r.bc.h * (r.kVloc * (r.KRb * r.M ^ 2 + r.Fb + r.epsA * r.M) + r.epsH * r.M))
    < (1 - r.epsI) * r.M

instance (r : BurnStep) : Decidable r.Valid := by unfold Valid; infer_instance

/-! ### Curves of the transported error dynamics -/

/-- The symplectic partner curve `H = realMat (hMat G)`. -/
def HfC (r : BurnStep) : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => realMat r.cc.H s
/-- The linearized state matrix curve `A(s) = Amat (q̂ s)`. -/
def AfC (r : BurnStep) : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => Amat (r.bc.toCandidate.pos s)
/-- The polynomial gradient candidate curve `Â`. -/
def AhfC (r : BurnStep) : ℝ → Matrix (Fin 4) (Fin 4) ℝ :=
  fun s => realMat (Ahat r.bc.toCandidate) s
/-- The derivative curve `H'`. -/
def HpfC (r : BurnStep) : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => realMat (pDeriv r.cc.H) s
/-- The deviation curve of a true motion `(Q, V)` with misalignment `δ`. -/
def efC (r : BurnStep) (Q V : ℝ → E2) (δ : ℝ) : ℝ → GNC.Transported.E :=
  fun s => BurnCandidate.dev r.bc Q V δ s
/-- The derivative curve of the deviation, with the thrust at the clamped time. -/
def edotC (r : BurnStep) (Q V : ℝ → E2) (δ : ℝ) (s : ℝ) : GNC.Transported.E :=
  join2 (V s - r.bc.toCandidate.dpos s - δ • r.bc.gv s)
    (Gravity.field 1 (Q s) + r.bc.thrustAcc δ (clampT (r.bc.h : ℝ) s)
      - r.bc.toCandidate.acc s - δ • r.bc.dgv s)
/-- The forcing curve `n = ė - A e`. -/
def nfC (r : BurnStep) (Q V : ℝ → E2) (δ : ℝ) (s : ℝ) : GNC.Transported.E :=
  r.edotC Q V δ s - GNC.Transported.act (r.AfC s) (r.efC Q V δ s)

theorem nfC_eq (r : BurnStep) (Q V : ℝ → E2) (δ s : ℝ) :
    r.nfC Q V δ s = join2 (0 : E2)
      ((Gravity.field 1 (Q s) + r.bc.thrustAcc δ (clampT (r.bc.h : ℝ) s)
          - r.bc.toCandidate.acc s - δ • r.bc.dgv s)
        - GNC.PlanarCoast.act (Dg (r.bc.toCandidate.pos s))
            (Q s - r.bc.toCandidate.pos s - δ • r.bc.gp s)) := by
  simp only [nfC, edotC, AfC, efC, BurnCandidate.dev, act_eq, act_Amat, join2_sub, sub_self]

theorem nfC_zero0 (r : BurnStep) (Q V : ℝ → E2) (δ s : ℝ) : (r.nfC Q V δ s) 0 = 0 := by
  rw [nfC_eq]; rfl

theorem nfC_zero1 (r : BurnStep) (Q V : ℝ → E2) (δ s : ℝ) : (r.nfC Q V δ s) 1 = 0 := by
  rw [nfC_eq]; rfl

/-- On the step the forcing curve is the forcing of `error_dynamics_burn`. -/
theorem nfC_eq_noise (r : BurnStep) (Q V : ℝ → E2) (δ : ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (r.bc.h : ℝ)) :
    r.nfC Q V δ s = BurnCandidate.noise r.bc Q V δ s := by
  rw [nfC_eq, clampT_of_mem hs]; rfl

theorem AfC_sub_AhfC_row0 (r : BurnStep) (s : ℝ) (k : Fin 4) :
    (r.AfC s - r.AhfC s) 0 k = 0 := Amat_sub_Ahat_row0 r.cc (r.bc.toCandidate.pos s) s k
theorem AfC_sub_AhfC_row1 (r : BurnStep) (s : ℝ) (k : Fin 4) :
    (r.AfC s - r.AhfC s) 1 k = 0 := Amat_sub_Ahat_row1 r.cc (r.bc.toCandidate.pos s) s k

/-! ### Derivative and continuity of the deviation -/

theorem gp_continuous (r : BurnStep) : Continuous r.bc.gp :=
  pack_continuous (ev_continuous _) (ev_continuous _)
theorem gv_continuous (r : BurnStep) : Continuous r.bc.gv :=
  pack_continuous (ev_continuous _) (ev_continuous _)
theorem dgv_continuous (r : BurnStep) : Continuous r.bc.dgv :=
  pack_continuous (ev_continuous _) (ev_continuous _)

/-- The deviation is differentiable on the step with derivative `A e + n`. -/
theorem efC_hasDerivAt (r : BurnStep) (hbc : r.bc.Valid) {Q V : ℝ → E2} {δ s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (r.bc.h : ℝ))
    (hQ : HasDerivAt Q (V s) s)
    (hV : HasDerivAt V (Gravity.field 1 (Q s) + r.bc.thrustAcc δ s) s) :
    HasDerivAt (r.efC Q V δ) (GNC.Transported.act (r.AfC s) (r.efC Q V δ s) + r.nfC Q V δ s) s := by
  have heq : GNC.Transported.act (r.AfC s) (r.efC Q V δ s) + r.nfC Q V δ s = r.edotC Q V δ s := by
    rw [nfC]; abel
  rw [heq, edotC, clampT_of_mem hs]
  have e1 : r.bc.gvx = differentiate r.bc.gx := hbc.2.2.2.2.2.2.2.1
  have e2 : r.bc.gvy = differentiate r.bc.gy := hbc.2.2.2.2.2.2.2.2
  have hgv : r.bc.gv s = r.bc.dgp s := by rw [BurnCandidate.gv, BurnCandidate.dgp, e1, e2]
  have hpos : HasDerivAt (fun s => Q s - r.bc.toCandidate.pos s - δ • r.bc.gp s)
      (V s - r.bc.toCandidate.dpos s - δ • r.bc.gv s) s := by
    have hp := (hQ.sub (r.bc.toCandidate.pos_hasDerivAt s)).sub
      ((r.bc.gp_hasDerivAt s).const_smul δ)
    rwa [hgv]
  have hvel : HasDerivAt (fun s => V s - r.bc.toCandidate.dpos s - δ • r.bc.gv s)
      (Gravity.field 1 (Q s) + r.bc.thrustAcc δ s - r.bc.toCandidate.acc s - δ • r.bc.dgv s) s :=
    (hV.sub (r.bc.toCandidate.dpos_hasDerivAt s)).sub ((r.bc.gv_hasDerivAt s).const_smul δ)
  exact join2_hasDerivAt hpos hvel

/-- The thrust at the clamped time is continuous on the whole line. -/
theorem thrust_clamp_continuous (r : BurnStep) (hbc : r.bc.Valid) (δ : ℝ) :
    Continuous (fun s => r.bc.thrustAcc δ (clampT (r.bc.h : ℝ) s)) := by
  have hh : (0 : ℝ) ≤ (r.bc.h : ℝ) := by exact_mod_cast hbc.1.1
  have hw : Continuous (fun s => r.bc.wReal (clampT (r.bc.h : ℝ) s)) := by
    unfold BurnCandidate.wReal
    refine continuous_const.div (continuous_const.sub (continuous_const.mul (clampT_continuous _)))
      ?_
    intro s
    exact (BurnCandidate.wDenom_pos r.bc hbc (clampT_mem hh s)).ne'
  unfold BurnCandidate.thrustAcc
  exact (continuous_const.mul hw).smul continuous_const

theorem efC_continuous (r : BurnStep) {Q V : ℝ → E2} (δ : ℝ) (hQc : Continuous Q)
    (hVc : Continuous V) : Continuous (r.efC Q V δ) :=
  join2_continuous ((hQc.sub r.bc.toCandidate.pos_continuous).sub
      (continuous_const.smul r.gp_continuous))
    ((hVc.sub r.bc.toCandidate.dpos_continuous).sub (continuous_const.smul r.gv_continuous))

theorem edotC_continuous (r : BurnStep) (hbc : r.bc.Valid) {Q V : ℝ → E2} (δ : ℝ)
    (hVc : Continuous V) (hfc : Continuous (fun s => Gravity.field 1 (Q s))) :
    Continuous (r.edotC Q V δ) :=
  join2_continuous ((hVc.sub r.bc.toCandidate.dpos_continuous).sub
      (continuous_const.smul r.gv_continuous))
    (((hfc.add (r.thrust_clamp_continuous hbc δ)).sub (acc_continuous r.bc.toCandidate)).sub
      (continuous_const.smul r.dgv_continuous))

/-- The transported drift of the step is continuous. -/
theorem driftC_continuous (r : BurnStep) (hbc : r.bc.Valid) {Q V : ℝ → E2} (δ : ℝ)
    (hQc : Continuous Q) (hVc : Continuous V)
    (hfc : Continuous (fun s => Gravity.field 1 (Q s))) :
    Continuous (GNC.Transported.drift r.HfC r.AfC r.HpfC (r.efC Q V δ) (r.nfC Q V δ)) := by
  have hdrift : GNC.Transported.drift r.HfC r.AfC r.HpfC (r.efC Q V δ) (r.nfC Q V δ)
      = fun s => GNC.Transported.act (r.HpfC s) (r.efC Q V δ s)
          + GNC.Transported.act (r.HfC s) (r.edotC Q V δ s) := by
    funext s
    have h1 : GNC.Transported.act (r.HpfC s + r.HfC s * r.AfC s) (r.efC Q V δ s)
        = GNC.Transported.act (r.HpfC s) (r.efC Q V δ s)
          + GNC.Transported.act (r.HfC s) (GNC.Transported.act (r.AfC s) (r.efC Q V δ s)) := by
      rw [GNC.Transported.act_add, GNC.Transported.act_mul]
    have h2 : GNC.Transported.act (r.HfC s) (r.nfC Q V δ s)
        = GNC.Transported.act (r.HfC s) (r.edotC Q V δ s)
          - GNC.Transported.act (r.HfC s) (GNC.Transported.act (r.AfC s) (r.efC Q V δ s)) := by
      rw [nfC]; exact map_sub (toEuclideanCLM (𝕜 := ℝ) (r.HfC s)) _ _
    show GNC.Transported.act (r.HpfC s + r.HfC s * r.AfC s) (r.efC Q V δ s)
        + GNC.Transported.act (r.HfC s) (r.nfC Q V δ s) = _
    rw [h1, h2]; abel
  rw [hdrift]
  exact (act_continuous (realMat_continuous _) (r.efC_continuous δ hQc hVc)).add
    (act_continuous (realMat_continuous _) (r.edotC_continuous hbc δ hVc hfc))

/-! ### Real bounds from the rational certificate -/

theorem kRcst_cast (r : BurnStep) :
    (r.kRcst : ℝ) = 3 / ((r.bc.rhoMin : ℝ) - (r.M : ℝ) - (r.bc.alpha : ℝ) * (r.bc.Gp : ℝ)) ^ 4 := by
  rw [kRcst]; push_cast; ring

/-- The forcing bound on the tube: inside `‖e‖ ≤ M`, `‖n‖ ≤ KRb ‖e‖² + Fb`. -/
theorem nfC_bound (r : BurnStep) (hr : r.Valid) {Q V : ℝ → E2} {δ : ℝ}
    (hδ : |δ| ≤ (r.bc.alpha : ℝ)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (r.bc.h : ℝ))
    (hQ : HasDerivAt Q (V s) s)
    (hV : HasDerivAt V (Gravity.field 1 (Q s) + r.bc.thrustAcc δ s) s)
    (hmem : ‖r.efC Q V δ s‖ ≤ (r.M : ℝ)) :
    ‖r.nfC Q V δ s‖ ≤ (r.KRb : ℝ) * ‖r.efC Q V δ s‖ ^ 2 + (r.Fb : ℝ) := by
  obtain ⟨hbc, _, _, hM0q, hMα, _, _, _, _, _, _, _, hkR, _, hFt, _⟩ := hr
  have hcond : (r.M : ℝ) + (r.bc.alpha : ℝ) * (r.bc.Gp : ℝ) < (r.bc.rhoMin : ℝ) := by
    exact_mod_cast hMα
  have hed := (BurnCandidate.error_dynamics_burn r.bc hbc hs hδ hcond hQ hV hmem).2.2.2
  rw [nfC_eq_noise r Q V δ hs]
  set ρ := ‖BurnCandidate.dev r.bc Q V δ s‖ with hρ
  have hefC : ‖r.efC Q V δ s‖ = ρ := rfl
  rw [hefC]
  set kR := (3 : ℝ) / ((r.bc.rhoMin : ℝ) - (r.M : ℝ) - (r.bc.alpha : ℝ) * (r.bc.Gp : ℝ)) ^ 4
    with hkRdef
  have hKd : kR ≤ (r.KRb : ℝ) := by rw [hkRdef, ← kRcst_cast r]; exact_mod_cast hkR
  have hα : (0 : ℝ) ≤ (r.bc.alpha : ℝ) := by exact_mod_cast hbc.2.2.2.2.2.1
  have hG : (0 : ℝ) ≤ (r.bc.Gp : ℝ) := by exact_mod_cast BurnCandidate.Gp_nonneg r.bc hbc
  have hM : (0 : ℝ) ≤ (r.M : ℝ) := by exact_mod_cast hM0q
  have hFtR : (r.FtotB : ℝ) ≤ (r.Fb : ℝ) := by exact_mod_cast hFt
  have hFtB : (r.FtotB : ℝ) = (r.bc.Fx : ℝ) + (r.bc.alpha : ℝ) * (r.bc.Fg : ℝ) + (r.bc.Fmis : ℝ)
      + (r.KRb : ℝ) * (r.bc.alpha : ℝ) ^ 2 * (r.bc.Gp : ℝ) ^ 2
      + 2 * (r.KRb : ℝ) * (r.bc.alpha : ℝ) * (r.bc.Gp : ℝ) * (r.M : ℝ) := by
    rw [FtotB]; push_cast; ring
  have e1 : kR * ρ ^ 2 ≤ (r.KRb : ℝ) * ρ ^ 2 := mul_le_mul_of_nonneg_right hKd (sq_nonneg _)
  have e2 : kR * (r.bc.alpha : ℝ) ^ 2 * (r.bc.Gp : ℝ) ^ 2
      ≤ (r.KRb : ℝ) * (r.bc.alpha : ℝ) ^ 2 * (r.bc.Gp : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKd (sq_nonneg _)) (sq_nonneg _)
  have e3 : 2 * kR * (r.bc.alpha : ℝ) * (r.bc.Gp : ℝ) * (r.M : ℝ)
      ≤ 2 * (r.KRb : ℝ) * (r.bc.alpha : ℝ) * (r.bc.Gp : ℝ) * (r.M : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hM
    apply mul_le_mul_of_nonneg_right _ hG
    apply mul_le_mul_of_nonneg_right _ hα
    linarith
  linarith [hed]

/-! ### Soundness of one certified step -/

/-- Soundness of one burn or coast step. For a valid record, a misalignment
`|δ| ≤ α` and a true motion `Q' = V`, `V' = g(Q) + f w(t) R(δ) e` on the step
with continuous position, velocity and gravity, whose initial deviation from the
segment `x̂ + δ ĝ` is at most `Ein`, the deviation stays strictly inside the tube
of radius `M` on the whole step. -/
theorem tube_sound (r : BurnStep) (hr : r.Valid) {δ : ℝ} (hδ : |δ| ≤ (r.bc.alpha : ℝ))
    {Q V : ℝ → E2} (hQc : Continuous Q) (hVc : Continuous V)
    (hfc : Continuous (fun s => Gravity.field 1 (Q s)))
    (hQ : ∀ s ∈ Icc (0 : ℝ) (r.bc.h : ℝ), HasDerivAt Q (V s) s)
    (hV : ∀ s ∈ Icc (0 : ℝ) (r.bc.h : ℝ),
      HasDerivAt V (Gravity.field 1 (Q s) + r.bc.thrustAcc δ s) s)
    (hE0 : ‖BurnCandidate.dev r.bc Q V δ 0‖ ≤ (r.Ein : ℝ)) :
    ∀ t ∈ Icc (0 : ℝ) (r.bc.h : ℝ), ‖BurnCandidate.dev r.bc Q V δ t‖ < (r.M : ℝ) := by
  have hr' := hr
  obtain ⟨hbc, hcc, hεI1q, hM0q, _, _, hEinM, _, _, _, _, hKRb0, _, hFb0, _, htube⟩ := hr'
  have hM0 : (0 : ℝ) ≤ (r.M : ℝ) := by exact_mod_cast hM0q
  have hK0 : (0 : ℝ) ≤ (r.KRb : ℝ) := by exact_mod_cast hKRb0
  have hF0 : (0 : ℝ) ≤ (r.Fb : ℝ) := by exact_mod_cast hFb0
  have hεI1 : (r.epsI : ℝ) < 1 := by exact_mod_cast hεI1q
  refine GNC.Transported.step_tube (fun s => realMat r.G s) r.HfC r.AfC r.AhfC r.HpfC
    (r.efC Q V δ) (r.nfC Q V δ)
    (M := (r.M : ℝ)) (K_R := (r.KRb : ℝ)) (F := (r.Fb : ℝ)) (εI := (r.epsI : ℝ))
    (ψ := (r.gSup : ℝ)) (kR := (r.epsH : ℝ)) (kV := (r.kVloc : ℝ)) (εA := (r.epsA : ℝ))
    (r.cc.H_zero hcc) ?hHd ?hed (r.efC_continuous δ hQc hVc)
    (r.driftC_continuous hbc δ hQc hVc hfc) hM0 hK0 hF0 hεI1
    (fun s k => r.AfC_sub_AhfC_row0 s k) (fun s k => r.AfC_sub_AhfC_row1 s k)
    (fun s => r.nfC_zero0 Q V δ s) (fun s => r.nfC_zero1 Q V δ s)
    ?hεI ?hψ ?hkR ?hkV ?hεA ?hnb ?hinit ?hclose
  case hHd => exact fun s _ => realMat_hasDerivAt r.cc.H s
  case hed => exact fun s hs => r.efC_hasDerivAt hbc hs (hQ s hs) (hV s hs)
  case hεI => exact fun t ht => r.cc.epsI_sound hcc ht
  case hψ => exact fun t ht => r.cc.gSup_sound hcc ht
  case hkR => exact fun s hs => r.cc.epsH_sound hcc hs
  case hkV =>
    intro s hs
    show GNC.Transported.frobVel (realMat r.cc.H s) ≤ (r.kVloc : ℝ)
    rw [frobVel_velCols]; exact r.cc.kV_sound hcc hs
  case hεA =>
    intro s hs
    show GNC.PlanarCoast.frob (Amat (r.cc.pos s) - realMat (Ahat r.cc.toCandidate) s)
      ≤ (r.cc.epsA : ℝ)
    rw [frob_Amat_sub_Ahat]; exact r.cc.epsA_sound hcc hs
  case hnb => exact fun s hs hmem => r.nfC_bound hr hδ hs (hQ s hs) (hV s hs) hmem
  case hinit => exact lt_of_le_of_lt hE0 (by exact_mod_cast hEinM)
  case hclose =>
    have hψ0 : (0 : ℝ) ≤ (r.gSup : ℝ) := le_trans (GNC.PlanarCoast.frob_nonneg _)
      (r.cc.gSup_sound hcc (left_mem_Icc.mpr (by exact_mod_cast hbc.1.1)))
    have htR : (r.gSup : ℝ) * ((r.Ein : ℝ) + (r.bc.h : ℝ) *
        ((r.kVloc : ℝ) * ((r.KRb : ℝ) * (r.M : ℝ) ^ 2 + (r.Fb : ℝ) + (r.epsA : ℝ) * (r.M : ℝ))
          + (r.epsH : ℝ) * (r.M : ℝ))) < (1 - (r.epsI : ℝ)) * (r.M : ℝ) := by
      exact_mod_cast htube
    have hmono : (r.gSup : ℝ) * (‖r.efC Q V δ 0‖ + (r.bc.h : ℝ) *
        ((r.kVloc : ℝ) * ((r.KRb : ℝ) * (r.M : ℝ) ^ 2 + (r.Fb : ℝ) + (r.epsA : ℝ) * (r.M : ℝ))
          + (r.epsH : ℝ) * (r.M : ℝ)))
        ≤ (r.gSup : ℝ) * ((r.Ein : ℝ) + (r.bc.h : ℝ) *
        ((r.kVloc : ℝ) * ((r.KRb : ℝ) * (r.M : ℝ) ^ 2 + (r.Fb : ℝ) + (r.epsA : ℝ) * (r.M : ℝ))
          + (r.epsH : ℝ) * (r.M : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hψ0
      have : ‖r.efC Q V δ 0‖ ≤ (r.Ein : ℝ) := hE0
      linarith
    show (r.gSup : ℝ) * (‖r.efC Q V δ 0‖ + (r.bc.h : ℝ) *
        ((r.kVloc : ℝ) * ((r.KRb : ℝ) * (r.M : ℝ) ^ 2 + (r.Fb : ℝ) + (r.epsA : ℝ) * (r.M : ℝ))
          + (r.epsH : ℝ) * (r.M : ℝ))) < (1 - (r.epsI : ℝ)) * (r.M : ℝ)
    linarith [htR, hmono]

/-! ### Per-step ingredients of the composed chain -/

/-- The gradient candidate error of the step. -/
theorem gradient_defect_bound (r : BurnStep) (hr : r.Valid) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (r.bc.h : ℝ)) :
    GNC.Transported.frob (r.AfC s - r.AhfC s) ≤ (r.epsA : ℝ) := by
  show GNC.PlanarCoast.frob (Amat (r.cc.pos s) - realMat (Ahat r.cc.toCandidate) s)
    ≤ (r.cc.epsA : ℝ)
  rw [frob_Amat_sub_Ahat]; exact r.cc.epsA_sound hr.2.1 hs

/-- The residual contraction of the step at the endpoint. -/
theorem residual_end (r : BurnStep) (hr : r.Valid) :
    GNC.Transported.frob (1 - realMat r.G (r.bc.h : ℝ) * r.HfC (r.bc.h : ℝ))
      ≤ (r.epsI : ℝ) := by
  have hh0 : (0 : ℝ) ≤ (r.bc.h : ℝ) := by exact_mod_cast hr.1.1.1
  exact r.cc.epsI_sound hr.2.1 (right_mem_Icc.mpr hh0)

/-- The exact transported step identity at the endpoint. -/
theorem step_identity_end (r : BurnStep) (hr : r.Valid) {Q V : ℝ → E2} (δ : ℝ)
    (hQc : Continuous Q) (hVc : Continuous V)
    (hfc : Continuous (fun s => Gravity.field 1 (Q s)))
    (hQ : ∀ s ∈ Icc (0 : ℝ) (r.bc.h : ℝ), HasDerivAt Q (V s) s)
    (hV : ∀ s ∈ Icc (0 : ℝ) (r.bc.h : ℝ),
      HasDerivAt V (Gravity.field 1 (Q s) + r.bc.thrustAcc δ s) s) :
    r.efC Q V δ (r.bc.h : ℝ)
      = GNC.Transported.act (realMat r.G (r.bc.h : ℝ))
          (r.efC Q V δ 0 + ∫ s in (0 : ℝ)..(r.bc.h : ℝ),
            GNC.Transported.drift r.HfC r.AfC r.HpfC (r.efC Q V δ) (r.nfC Q V δ) s)
        + GNC.Transported.act (1 - realMat r.G (r.bc.h : ℝ) * r.HfC (r.bc.h : ℝ))
            (r.efC Q V δ (r.bc.h : ℝ)) := by
  have hh0 : (0 : ℝ) ≤ (r.bc.h : ℝ) := by exact_mod_cast hr.1.1.1
  refine GNC.Transported.step_identity (fun s => realMat r.G s) r.HfC r.AfC r.HpfC
    (r.efC Q V δ) (r.nfC Q V δ) (r.cc.H_zero hr.2.1) ?hHd ?hed
    (r.driftC_continuous hr.1 δ hQc hVc hfc) (t := (r.bc.h : ℝ)) Set.right_mem_uIcc
  case hHd => exact fun s _ => realMat_hasDerivAt r.cc.H s
  case hed =>
    intro s hs
    rw [uIcc_of_le hh0] at hs
    exact r.efC_hasDerivAt hr.1 hs (hQ s hs) (hV s hs)

/-- The endpoint transition equals the stored evaluated transition, cast. -/
theorem P_eq (r : BurnStep) (hr : r.Valid) :
    realMat r.G (r.bc.h : ℝ) = (r.Pev).map (Rat.cast : ℚ → ℝ) := by
  have hPev : r.Pev = evalMatQ r.G r.bc.h := hr.2.2.2.2.2.2.2.1
  ext i j
  rw [Matrix.map_apply, hPev, evalMatQ]
  exact ev_ratEval (r.G i j) r.bc.h

/-! ### The handoff mismatch -/

/-- The squared jump of the nominal candidate (position and its derivative)
between two consecutive steps. -/
def jumpSqX (a b : BurnStep) : ℚ :=
  (evaluate a.bc.x a.bc.h - evaluate b.bc.x 0) ^ 2
    + (evaluate a.bc.y a.bc.h - evaluate b.bc.y 0) ^ 2
    + (evaluate (differentiate a.bc.x) a.bc.h - evaluate (differentiate b.bc.x) 0) ^ 2
    + (evaluate (differentiate a.bc.y) a.bc.h - evaluate (differentiate b.bc.y) 0) ^ 2

/-- The squared jump of the sensitivity candidate between two consecutive steps. -/
def jumpSqG (a b : BurnStep) : ℚ :=
  (evaluate a.bc.gx a.bc.h - evaluate b.bc.gx 0) ^ 2
    + (evaluate a.bc.gy a.bc.h - evaluate b.bc.gy 0) ^ 2
    + (evaluate a.bc.gvx a.bc.h - evaluate b.bc.gvx 0) ^ 2
    + (evaluate a.bc.gvy a.bc.h - evaluate b.bc.gvy 0) ^ 2

/-- A rational square witness bounds the norm of a stacked vector of four
rational evaluations. -/
theorem join2_pack_norm_le (a b c e : ℝ) (B : ℚ) (hB0 : 0 ≤ B)
    (hsq : a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 ≤ (B : ℝ) ^ 2) :
    ‖join2 (pack a b) (pack c e)‖ ≤ (B : ℝ) := by
  have hB : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB0
  have hn : ‖join2 (pack a b) (pack c e)‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 := by
    rw [join2_norm_sq, pack_norm_sq, pack_norm_sq]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).mp (hn ▸ hsq)

/-- The handoff mismatch of the deviation between two consecutive steps sharing
the true motion across the junction is at most `dX + α dG`. -/
theorem handoff (a b : BurnStep) (hb : b.Valid) {Q V Q' V' : ℝ → E2} {δ : ℝ}
    (hδ : |δ| ≤ (b.bc.alpha : ℝ))
    (hjQ : Q' 0 = Q (a.bc.h : ℝ)) (hjV : V' 0 = V (a.bc.h : ℝ))
    (hX : jumpSqX a b ≤ b.dX ^ 2) (hG : jumpSqG a b ≤ b.dG ^ 2) :
    ‖b.efC Q' V' δ 0 - a.efC Q V δ (a.bc.h : ℝ)‖ ≤ (b.d : ℝ) := by
  have hz : (0 : ℝ) = ((0 : ℚ) : ℝ) := by norm_num
  set jc : GNC.Transported.E :=
    join2 (a.bc.toCandidate.pos (a.bc.h : ℝ) - b.bc.toCandidate.pos 0)
      (a.bc.toCandidate.dpos (a.bc.h : ℝ) - b.bc.toCandidate.dpos 0) with hjc
  set js : GNC.Transported.E :=
    join2 (a.bc.gp (a.bc.h : ℝ) - b.bc.gp 0) (a.bc.gv (a.bc.h : ℝ) - b.bc.gv 0) with hjs
  have hsplit : b.efC Q' V' δ 0 - a.efC Q V δ (a.bc.h : ℝ) = jc + δ • js := by
    simp only [efC, BurnCandidate.dev, hjQ, hjV, hjc, hjs, join2_sub]
    ext i; fin_cases i <;>
      simp [join2, pack4, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply] <;> ring
  have hjcB : ‖jc‖ ≤ (b.dX : ℝ) := by
    rw [hjc, Candidate.pos, Candidate.pos, pack_sub, Candidate.dpos, Candidate.dpos, pack_sub]
    refine join2_pack_norm_le _ _ _ _ _ hb.2.2.2.2.2.2.2.2.1 ?_
    rw [ev_ratEval a.bc.x a.bc.h, ev_ratEval a.bc.y a.bc.h,
      ev_ratEval (differentiate a.bc.x) a.bc.h, ev_ratEval (differentiate a.bc.y) a.bc.h,
      hz, ev_ratEval b.bc.x 0, ev_ratEval b.bc.y 0,
      ev_ratEval (differentiate b.bc.x) 0, ev_ratEval (differentiate b.bc.y) 0]
    have := (Rat.cast_le (K := ℝ)).mpr hX
    rw [jumpSqX] at this; push_cast at this ⊢; linarith
  have hjsB : ‖js‖ ≤ (b.dG : ℝ) := by
    rw [hjs, BurnCandidate.gp, BurnCandidate.gp, pack_sub, BurnCandidate.gv, BurnCandidate.gv,
      pack_sub]
    refine join2_pack_norm_le _ _ _ _ _ hb.2.2.2.2.2.2.2.2.2.1 ?_
    rw [ev_ratEval a.bc.gx a.bc.h, ev_ratEval a.bc.gy a.bc.h,
      ev_ratEval a.bc.gvx a.bc.h, ev_ratEval a.bc.gvy a.bc.h,
      hz, ev_ratEval b.bc.gx 0, ev_ratEval b.bc.gy 0,
      ev_ratEval b.bc.gvx 0, ev_ratEval b.bc.gvy 0]
    have := (Rat.cast_le (K := ℝ)).mpr hG
    rw [jumpSqG] at this; push_cast at this ⊢; linarith
  have hd : (b.d : ℝ) = (b.dX : ℝ) + (b.bc.alpha : ℝ) * (b.dG : ℝ) := by
    rw [hb.2.2.2.2.2.2.2.2.2.2.1]; push_cast; ring
  rw [hsplit, hd]
  exact GNC.PlanarBurn.handoff_bound jc js δ _ _ _ hjcB hjsB hδ

end BurnStep
end GNC.Applications.CertifiedBurn
