import GNC.Analysis.TransportedCertificate
import GNC.Dynamics.PlanarCoastCurvature

/-! One certified coast step of the curvature (transition-matrix) certificate.
A `StepRecord` bundles a `CurvatureCandidate` with the rational data of the
transported certificate: the handoff radius `d` bounding the mismatch of the
candidate at the step junction, the tube radius `M`, the node input `Ein`
bounding the initial error of the step, the exact rational evaluation `Pev` of
the transition candidate at the step endpoint, and, for the position, velocity
and full row sets, the per-pair Frobenius bounds of the composed transitions
that the chain node bound consumes. The decidable `Valid` predicate checks the
base candidate certificate, the residual contraction `epsI < 1`, and the first
exit tube closure inequality; `tube_sound` transports it to a real tube bound
through `step_tube` and `error_dynamics`. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Finset Matrix
open GNC.Planning.PolynomialKernel GNC.PolynomialBounds
open scoped Matrix.Norms.L2Operator
namespace GNC.Applications.CertifiedCoast.Curvature
open GNC.PlanarCoast GNC.PlanarCoast.Candidate GNC.PlanarCoast.CurvatureCandidate

/-! ### Exact rational evaluation of a polynomial matrix -/

/-- Entrywise rational evaluation of a polynomial matrix at a rational time. -/
def evalMatQ (P : PolyMat) (t : ℚ) : Matrix (Fin 4) (Fin 4) ℚ := fun i j => evaluate (P i j) t

/-! ### Derivative and continuity of a polynomial matrix curve -/

/-- A polynomial matrix curve is differentiable, with the entrywise derivative
polynomial matrix as its derivative, in the operator norm. -/
theorem realMat_hasDerivAt (P : PolyMat) (t : ℝ) :
    HasDerivAt (realMat P) (realMat (pDeriv P) t) t := by
  have hrw : (realMat P) = fun s => ∑ i : Fin 4, ∑ j : Fin 4,
      (ev (P i j) s) • Matrix.single i j (1:ℝ) := by
    funext s
    conv_lhs => rw [matrix_eq_sum_single (realMat P s)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (realMat P s) i j = ev (P i j) s from rfl, smul_single, smul_eq_mul, mul_one]
  rw [hrw]
  have hd : HasDerivAt (fun s => ∑ i : Fin 4, ∑ j : Fin 4,
        (ev (P i j) s) • Matrix.single i j (1:ℝ))
      (∑ i : Fin 4, ∑ j : Fin 4, (ev (differentiate (P i j)) t) • Matrix.single i j (1:ℝ)) t :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        (ev_hasDerivAt (P i j) t).smul_const _
  convert hd using 1
  rw [matrix_eq_sum_single (realMat (pDeriv P) t)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show realMat (pDeriv P) t i j = ev (differentiate (P i j)) t from rfl,
    smul_single, smul_eq_mul, mul_one]

/-- A polynomial matrix curve is continuous in the operator norm. -/
theorem realMat_continuous (P : PolyMat) : Continuous (realMat P) :=
  continuous_iff_continuousAt.mpr fun t => (realMat_hasDerivAt P t).continuousAt

/-! ### Continuity of the transported action and the stacked curves -/

/-- The velocity-column Frobenius norm equals the full Frobenius norm of the
velocity-column restriction. -/
theorem frobVel_velCols (H : PolyMat) (t : ℝ) :
    GNC.Transported.frobVel (realMat H t) = GNC.PlanarCoast.frob (realMat (velCols H) t) := by
  rw [GNC.Transported.frobVel, GNC.PlanarCoast.frob]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_pair (show (2:Fin 4) ≠ 3 by decide), Fin.sum_univ_four]
  have e0 : realMat (velCols H) t i 0 = 0 := by simp [realMat, velCols, ev_nil]
  have e1 : realMat (velCols H) t i 1 = 0 := by simp [realMat, velCols, ev_nil]
  have e2 : realMat (velCols H) t i 2 = realMat H t i 2 := by simp [realMat, velCols]
  have e3 : realMat (velCols H) t i 3 = realMat H t i 3 := by simp [realMat, velCols]
  rw [e0, e1, e2, e3]; ring

/-- The transported action and the plane action agree on the state space. -/
theorem act_eq (M : Matrix (Fin 4) (Fin 4) ℝ) (v : GNC.Transported.E) :
    GNC.Transported.act M v = GNC.PlanarCoast.act M v := rfl

/-- The transported matrix action is jointly continuous along continuous
matrix and vector curves. -/
theorem act_continuous {M : ℝ → Matrix (Fin 4) (Fin 4) ℝ} {v : ℝ → GNC.Transported.E}
    (hM : Continuous M) (hv : Continuous v) :
    Continuous (fun s => GNC.Transported.act (M s) (v s)) := by
  have h : Continuous (fun s =>
      (toEuclideanCLM (𝕜 := ℝ) (M s) : GNC.Transported.E →L[ℝ] GNC.Transported.E)) :=
    GNC.Transported.actL.toContinuousLinearMap.continuous.comp hM
  exact h.clm_apply hv

/-- Evaluation of a continuous plane curve at a coordinate is continuous. -/
theorem e2_apply_continuous {X : ℝ → E2} (hX : Continuous X) (i : Fin 2) :
    Continuous (fun s => (X s) i) :=
  ((continuous_apply i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).continuous).comp hX

/-- Stacking two continuous plane curves is continuous. -/
theorem join2_continuous {X Y : ℝ → E2} (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun s => join2 (X s) (Y s)) := by
  have hpi : Continuous (fun s => (![X s 0, X s 1, Y s 0, Y s 1] : Fin 4 → ℝ)) := by
    apply continuous_pi; intro i
    fin_cases i
    · exact e2_apply_continuous hX 0
    · exact e2_apply_continuous hX 1
    · exact e2_apply_continuous hY 0
    · exact e2_apply_continuous hY 1
  exact ((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap.continuous).comp hpi

/-- Stacking two continuous scalar curves into a plane curve is continuous. -/
theorem pack_continuous {X Y : ℝ → ℝ} (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun s => pack (X s) (Y s)) := by
  have hpi : Continuous (fun s => (![X s, Y s] : Fin 2 → ℝ)) := by
    apply continuous_pi; intro i; fin_cases i <;> simpa
  exact ((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.continuous).comp hpi

/-- The candidate acceleration curve is continuous. -/
theorem acc_continuous (c : Candidate) : Continuous c.acc :=
  pack_continuous (ev_continuous _) (ev_continuous _)

/-- The packed true position curve is continuous. -/
theorem truePos_continuous {w : ℝ → Fin 4 → ℝ} (hw : Continuous w) : Continuous (truePos w) :=
  pack_continuous ((continuous_apply 0).comp hw) ((continuous_apply 1).comp hw)

/-- The packed true velocity curve is continuous. -/
theorem trueVel_continuous {w : ℝ → Fin 4 → ℝ} (hw : Continuous w) : Continuous (trueVel w) :=
  pack_continuous ((continuous_apply 2).comp hw) ((continuous_apply 3).comp hw)

/-! ### Structure of the state matrix and the gradient candidate -/

/-- Real evaluation of a scaled polynomial. -/
theorem ev_scale (q : ℚ) (p : List ℚ) (t : ℝ) : ev (scale q p) t = (q:ℝ) * ev p t := by
  unfold ev; rw [scale_map, evaluate_scale]; norm_num

/-- Difference of two stacked plane vectors. -/
theorem join2_sub (x y x' y' : E2) : join2 x y - join2 x' y' = join2 (x - x') (y - y') := by
  ext i; fin_cases i <;> rfl

/-- The top two rows of the state matrix `A(q)` and the gradient candidate
`Â` coincide, so their difference vanishes there. -/
theorem Amat_sub_Ahat_row0 (cc : CurvatureCandidate) (q : E2) (s : ℝ) (j : Fin 4) :
    (Amat q - realMat (Ahat cc.toCandidate) s) 0 j = 0 := by
  fin_cases j <;>
    simp [Matrix.sub_apply, Amat, Ahat, realMat, ev_cons, ev_nil]

theorem Amat_sub_Ahat_row1 (cc : CurvatureCandidate) (q : E2) (s : ℝ) (j : Fin 4) :
    (Amat q - realMat (Ahat cc.toCandidate) s) 1 j = 0 := by
  fin_cases j <;>
    simp [Matrix.sub_apply, Amat, Ahat, realMat, ev_cons, ev_nil]

/-- The `4×4` gradient defect `A(q̂) − Â` is supported on the lower-left block,
where it equals the `2×2` gradient defect `Dg(q̂) − Â_lower`, so their Frobenius
norms agree. -/
theorem frob_Amat_sub_Ahat (cc : CurvatureCandidate) (s : ℝ) :
    GNC.PlanarCoast.frob (Amat (cc.pos s) - realMat (Ahat cc.toCandidate) s)
      = GNC.PlanarCoast.frob (Dg (cc.pos s) - Alower cc.toCandidate s) := by
  unfold GNC.PlanarCoast.frob
  congr 1
  simp only [Fin.sum_univ_four, Fin.sum_univ_two, Matrix.sub_apply, Amat, Ahat, realMat, Dg,
    Alower, ev_subtract, ev_multiply, ev_scale, ev_cons, ev_nil, invRadius, Candidate.pos,
    pack_apply_zero, pack_apply_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq,
    Candidate.u3, if_true, if_false, ite_true, ite_false]
  ring

/-! ### The certified step record -/

/-- One curvature-certificate step: a `CurvatureCandidate` with the rational
handoff radius, tube radius, node input, the evaluated local transition, and
the per-pair composed-transition Frobenius bounds for the full, position and
velocity row sets. -/
structure StepRecord where
  cc : CurvatureCandidate
  /-- Bound on the handoff mismatch `‖m‖` at the start of the step. -/
  d : ℚ
  /-- Tube radius of the step. -/
  M : ℚ
  /-- Bound on the initial error `‖e 0‖` of the step. -/
  Ein : ℚ
  /-- Small-denominator upper bound of the candidate defect. -/
  Fb : ℚ
  /-- Small-denominator upper bound of the field remainder constant
  `3 / (rhoMin - M)^4`. -/
  KRb : ℚ
  /-- Exact rational evaluation of the transition candidate at the endpoint. -/
  Pev : Matrix (Fin 4) (Fin 4) ℚ
  /-- Full-row bounds `frob (Φ i j)`, indexed by `j`. -/
  kM : List ℚ
  /-- Full-row slack bounds `frob (Φ i (j+1))`, indexed by `j`. -/
  kS : List ℚ
  /-- Full-row velocity-column kernel bounds `frobVel (Φ i j * H j)`. -/
  kV : List ℚ
  /-- Full-row derivative kernel bounds `frob (Φ i j * (H' + H Â) j)`. -/
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
  /-- Column-split bounds of the initial composed transition `Φ i 0`: the
  position-column (`0, 1`) and velocity-column (`2, 3`) Frobenius norms of the
  row block, transporting the position and velocity initial radii separately.
  Indexed by the row set (full, position, velocity). -/
  kM0p : ℚ
  kM0v : ℚ
  kMp0p : ℚ
  kMp0v : ℚ
  kMv0p : ℚ
  kMv0v : ℚ

namespace StepRecord

/-- The second-order field remainder constant on the tube, matching
`field_taylor_remainder`: `K_R = 3 / (rhoMin - M)^4`. -/
def kRcst (r : StepRecord) : ℚ := 3 / (r.cc.rhoMin - r.M) ^ 4

/-- The candidate acceleration defect, the constant forcing of the tube. -/
def defect (r : StepRecord) : ℚ := r.cc.toCandidate.defect

/-- The decidable rational hypotheses that certify one step: the base
curvature certificate, the residual contraction, the tube geometry, the
soundness of the small-denominator forcing and remainder bounds against the
exact candidate defect and remainder constant, and the first exit tube
closure inequality written entirely with the small bounds so that the kernel
decides it without normalizing the exact large rationals. -/
def Valid (r : StepRecord) : Prop :=
  r.cc.Valid ∧ r.cc.epsI < 1 ∧ 0 ≤ r.M ∧ r.M < r.cc.rhoMin ∧ 0 ≤ r.Ein ∧ r.Ein < r.M ∧
  r.Pev = evalMatQ r.cc.G r.cc.h ∧
  0 ≤ r.Fb ∧ r.defect ≤ r.Fb ∧ 0 ≤ r.KRb ∧ r.kRcst ≤ r.KRb ∧
  r.cc.gSup * (r.Ein + r.cc.h *
      (r.cc.kV * (r.KRb * r.M ^ 2 + r.Fb + r.cc.epsA * r.M) + r.cc.epsH * r.M))
    < (1 - r.cc.epsI) * r.M

instance (r : StepRecord) : Decidable r.Valid := by unfold Valid; infer_instance

/-! ### Real bound of the field remainder constant -/

theorem kRcst_cast (r : StepRecord) (h : r.M < r.cc.rhoMin) :
    (r.kRcst : ℝ) = 3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4 := by
  have hne : (r.cc.rhoMin : ℝ) - (r.M : ℝ) ≠ 0 := by
    have : (r.M : ℝ) < (r.cc.rhoMin : ℝ) := by exact_mod_cast h
    linarith
  rw [kRcst]; push_cast; ring

/-- Position error is bounded by the full state error. -/
theorem norm_posErr_le (x y : E2) : ‖x‖ ≤ ‖join2 x y‖ := by
  have h : ‖x‖ ^ 2 ≤ ‖join2 x y‖ ^ 2 := by
    rw [join2_norm_sq]; nlinarith [norm_nonneg y]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-! ### Soundness of one certified step -/

/-- Soundness of one curvature-certificate step. Given a valid record, a true
inverse-square solution with continuous state and continuous acceleration whose
initial error lies within `Ein`, the transported error stays strictly inside
the tube of radius `M` on the whole step. This instantiates the first exit
`step_tube` with the linearized error dynamics of `error_dynamics`, using the
symplectic transition candidate `Ψ = realMat G`, its symplectic partner
`H = realMat (hMat G)`, and the polynomial gradient candidate `Â`. -/
theorem tube_sound (r : StepRecord) (hr : r.Valid) (w : ℝ → Fin 4 → ℝ)
    (hwc : Continuous w)
    (hw : ∀ s ∈ Icc (0:ℝ) (r.cc.h:ℝ), HasDerivAt w (PolynomialOrbit.physicalRate 0 (w s)) s)
    (hacc : Continuous (fun s => Gravity.field 1 (truePos w s)))
    (hE0 : ‖join2 (truePos w 0 - r.cc.pos 0) (trueVel w 0 - r.cc.dpos 0)‖ ≤ (r.Ein : ℝ)) :
    ∀ t ∈ Icc (0:ℝ) (r.cc.h:ℝ),
      ‖join2 (truePos w t - r.cc.pos t) (trueVel w t - r.cc.dpos t)‖ < (r.M : ℝ) := by
  obtain ⟨hcc, hepsI1, hM0q, hMrho, hEin0, hEinM, hPev, hFb0, hdefFb, hKRb0, hkRcst, htube⟩ := hr
  -- real casts
  have hMrhoR : (r.M : ℝ) < (r.cc.rhoMin : ℝ) := by exact_mod_cast hMrho
  have hM0 : (0:ℝ) ≤ (r.M : ℝ) := by exact_mod_cast hM0q
  have hK0 : (0:ℝ) ≤ (r.KRb : ℝ) := by exact_mod_cast hKRb0
  have hF0 : (0:ℝ) ≤ (r.Fb : ℝ) := by exact_mod_cast hFb0
  have hεI1 : (r.cc.epsI : ℝ) < 1 := by exact_mod_cast hepsI1
  have hKRcst : (3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4) ≤ (r.KRb : ℝ) := by
    rw [← kRcst_cast r hMrho]; exact_mod_cast hkRcst
  -- the transported functions
  set Ψ : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => realMat r.cc.G s with hΨ
  set Hm : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => realMat r.cc.H s with hHm
  set Am : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => Amat (r.cc.pos s) with hAm
  set Âm : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => realMat (Ahat r.cc.toCandidate) s with hÂm
  set H'm : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => realMat (pDeriv r.cc.H) s with hH'm
  set e : ℝ → GNC.Transported.E := fun s => join2 (truePos w s - r.cc.pos s) (trueVel w s - r.cc.dpos s) with he
  set edot : ℝ → GNC.Transported.E :=
    fun s => join2 (trueVel w s - r.cc.dpos s) (Gravity.field 1 (truePos w s) - r.cc.acc s) with hedot
  set n : ℝ → GNC.Transported.E := fun s => edot s - GNC.Transported.act (Am s) (e s) with hn
  -- forcing has zero position block and equals the field remainder
  have hforce : ∀ s, n s = join2 (0 : E2)
      (Gravity.field 1 (truePos w s) - r.cc.acc s
        - GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s)) := by
    intro s
    have hact : GNC.Transported.act (Am s) (e s)
        = join2 (trueVel w s - r.cc.dpos s) (GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s)) := by
      simp only [hAm, he, act_eq, act_Amat]
    rw [hn]; simp only [hedot, hact, join2_sub, sub_self]
  have hn0 : ∀ s, (n s) 0 = 0 := fun s => by rw [hforce]; rfl
  have hn1 : ∀ s, (n s) 1 = 0 := fun s => by rw [hforce]; rfl
  -- e is differentiable on the step with derivative edot
  have hed : ∀ s ∈ Icc (0:ℝ) (r.cc.h:ℝ),
      HasDerivAt e (GNC.Transported.act (Am s) (e s) + n s) s := by
    intro s hs
    have : GNC.Transported.act (Am s) (e s) + n s = edot s := by simp only [hn]; abel
    rw [this]
    exact join2_hasDerivAt (r.cc.toCandidate.errorPos_hasDerivAt (hw s hs))
      (r.cc.toCandidate.errorVel_hasDerivAt (hw s hs))
  -- continuity of e and of the drift (A cancels)
  have hcTP : Continuous (truePos w) := truePos_continuous hwc
  have hcTV : Continuous (trueVel w) := trueVel_continuous hwc
  have hce : Continuous e :=
    join2_continuous (hcTP.sub r.cc.toCandidate.pos_continuous)
      (hcTV.sub r.cc.toCandidate.dpos_continuous)
  have hcedot : Continuous edot :=
    join2_continuous (hcTV.sub r.cc.toCandidate.dpos_continuous)
      (hacc.sub (acc_continuous r.cc.toCandidate))
  have hcont : Continuous (GNC.Transported.drift Hm Am H'm e n) := by
    have hdrift : GNC.Transported.drift Hm Am H'm e n
        = fun s => GNC.Transported.act (H'm s) (e s) + GNC.Transported.act (Hm s) (edot s) := by
      funext s
      have h1 : GNC.Transported.act (H'm s + Hm s * Am s) (e s)
          = GNC.Transported.act (H'm s) (e s)
            + GNC.Transported.act (Hm s) (GNC.Transported.act (Am s) (e s)) := by
        rw [GNC.Transported.act_add, GNC.Transported.act_mul]
      have h2 : GNC.Transported.act (Hm s) (n s)
          = GNC.Transported.act (Hm s) (edot s)
            - GNC.Transported.act (Hm s) (GNC.Transported.act (Am s) (e s)) := by
        simp only [hn]
        exact map_sub (toEuclideanCLM (𝕜 := ℝ) (Hm s)) _ _
      show GNC.Transported.act (H'm s + Hm s * Am s) (e s) + GNC.Transported.act (Hm s) (n s)
          = GNC.Transported.act (H'm s) (e s) + GNC.Transported.act (Hm s) (edot s)
      rw [h1, h2]; abel
    rw [hdrift]
    exact (act_continuous (realMat_continuous _) hce).add
      (act_continuous (realMat_continuous _) hcedot)
  -- apply the first exit tube
  refine GNC.Transported.step_tube Ψ Hm Am Âm H'm e n
    (M := (r.M:ℝ)) (K_R := (r.KRb:ℝ)) (F := (r.Fb:ℝ)) (εI := (r.cc.epsI:ℝ)) (ψ := (r.cc.gSup:ℝ))
    (kR := (r.cc.epsH:ℝ)) (kV := (r.cc.kV:ℝ)) (εA := (r.cc.epsA:ℝ))
    (r.cc.H_zero hcc) ?hHd hed hce hcont hM0 hK0 hF0 hεI1
    ?hAp0 ?hAp1 hn0 hn1 ?hεI ?hψ ?hkR ?hkV ?hεA ?hnb ?hinit ?hclose
  case hHd => exact fun s _ => realMat_hasDerivAt r.cc.H s
  case hAp0 => exact fun s j => Amat_sub_Ahat_row0 r.cc (r.cc.pos s) s j
  case hAp1 => exact fun s j => Amat_sub_Ahat_row1 r.cc (r.cc.pos s) s j
  case hεI => exact fun t ht => r.cc.epsI_sound hcc ht
  case hψ => exact fun t ht => r.cc.gSup_sound hcc ht
  case hkR => exact fun s hs => r.cc.epsH_sound hcc hs
  case hkV =>
    intro s hs
    simp only [hHm]
    rw [frobVel_velCols]; exact r.cc.kV_sound hcc hs
  case hεA =>
    intro s hs
    simp only [hAm, hÂm]
    show GNC.PlanarCoast.frob (Amat (r.cc.pos s) - realMat (Ahat r.cc.toCandidate) s) ≤ (r.cc.epsA : ℝ)
    rw [frob_Amat_sub_Ahat]; exact r.cc.epsA_sound hcc hs
  case hnb =>
    intro s hs hmem
    rw [hforce s, join2_left_zero_norm]
    have hqrad : (r.cc.rhoMin : ℝ) ≤ ‖r.cc.pos s‖ :=
      r.cc.toCandidate.rhoMin_le_norm_pos hcc.1 hs
    have hposb : ‖truePos w s - r.cc.pos s‖ ≤ (r.M : ℝ) :=
      le_trans (norm_posErr_le _ _) hmem
    have hrem := field_taylor_remainder (r.cc.pos s) (truePos w s - r.cc.pos s)
      hMrhoR hqrad hposb
    have hsplit : Gravity.field 1 (truePos w s) - r.cc.acc s
          - GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s)
        = (Gravity.field 1 (r.cc.pos s + (truePos w s - r.cc.pos s)) - Gravity.field 1 (r.cc.pos s)
            - GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s))
          + (Gravity.field 1 (r.cc.pos s) - r.cc.acc s) := by
      rw [add_sub_cancel]; abel
    have hdef : ‖Gravity.field 1 (r.cc.pos s) - r.cc.acc s‖ ≤ (r.defect : ℝ) := by
      rw [norm_sub_rev]; exact r.cc.toCandidate.defect_bound hcc.1 hs
    have hb1 : ‖Gravity.field 1 (truePos w s) - r.cc.acc s
          - GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s)‖
        ≤ (3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4) * ‖truePos w s - r.cc.pos s‖ ^ 2 + (r.defect : ℝ) := by
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add hrem hdef)
    have hesM : ‖e s‖ ≤ (r.M : ℝ) := hmem
    have hKRnn : (0:ℝ) ≤ 3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4 := by
      have : (r.M : ℝ) < (r.cc.rhoMin : ℝ) := hMrhoR; positivity
    have hp2 : ‖truePos w s - r.cc.pos s‖ ^ 2 ≤ ‖e s‖ ^ 2 := by
      have hle := norm_posErr_le (truePos w s - r.cc.pos s) (trueVel w s - r.cc.dpos s)
      simp only [he]
      nlinarith [hle, norm_nonneg (truePos w s - r.cc.pos s)]
    have hdefFbR : (r.defect : ℝ) ≤ (r.Fb : ℝ) := by exact_mod_cast hdefFb
    calc ‖Gravity.field 1 (truePos w s) - r.cc.acc s
            - GNC.PlanarCoast.act (Dg (r.cc.pos s)) (truePos w s - r.cc.pos s)‖
        ≤ (3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4) * ‖truePos w s - r.cc.pos s‖ ^ 2 + (r.defect : ℝ) := hb1
      _ ≤ (r.KRb : ℝ) * ‖e s‖ ^ 2 + (r.Fb : ℝ) := by
            apply add_le_add _ hdefFbR
            calc (3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4) * ‖truePos w s - r.cc.pos s‖ ^ 2
                ≤ (3 / ((r.cc.rhoMin : ℝ) - (r.M : ℝ)) ^ 4) * ‖e s‖ ^ 2 :=
                  mul_le_mul_of_nonneg_left hp2 hKRnn
              _ ≤ (r.KRb : ℝ) * ‖e s‖ ^ 2 :=
                  mul_le_mul_of_nonneg_right hKRcst (by positivity)
  case hinit => exact lt_of_le_of_lt hE0 (by exact_mod_cast hEinM)
  case hclose =>
    have hψ0 : (0:ℝ) ≤ (r.cc.gSup : ℝ) := le_trans (GNC.PlanarCoast.frob_nonneg _)
      (r.cc.gSup_sound hcc (left_mem_Icc.mpr (by exact_mod_cast hcc.1.1)))
    have htR : (r.cc.gSup : ℝ) * ((r.Ein : ℝ) + (r.cc.h : ℝ) *
        ((r.cc.kV : ℝ) * ((r.KRb : ℝ) * (r.M : ℝ) ^ 2 + (r.Fb : ℝ) + (r.cc.epsA : ℝ) * (r.M : ℝ))
          + (r.cc.epsH : ℝ) * (r.M : ℝ))) < (1 - (r.cc.epsI : ℝ)) * (r.M : ℝ) := by
      exact_mod_cast htube
    have hmono : (r.cc.gSup : ℝ) * (‖e 0‖ + (r.cc.h : ℝ) *
        ((r.cc.kV : ℝ) * ((r.KRb : ℝ) * (r.M : ℝ) ^ 2 + (r.Fb : ℝ) + (r.cc.epsA : ℝ) * (r.M : ℝ))
          + (r.cc.epsH : ℝ) * (r.M : ℝ)))
        ≤ (r.cc.gSup : ℝ) * ((r.Ein : ℝ) + (r.cc.h : ℝ) *
        ((r.cc.kV : ℝ) * ((r.KRb : ℝ) * (r.M : ℝ) ^ 2 + (r.Fb : ℝ) + (r.cc.epsA : ℝ) * (r.M : ℝ))
          + (r.cc.epsH : ℝ) * (r.M : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hψ0
      have : ‖e 0‖ ≤ (r.Ein : ℝ) := by rw [he]; exact hE0
      linarith
    linarith [htR, hmono]

end StepRecord
end GNC.Applications.CertifiedCoast.Curvature
