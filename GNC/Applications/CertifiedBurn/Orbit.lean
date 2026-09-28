import GNC.Applications.CertifiedBurn.Checks.Mf
import GNC.Applications.CertifiedBurn.Checks.Vf
import GNC.Applications.CertifiedBurn.Checks.If
import GNC.Applications.CertifiedBurn.Checks.Mp
import GNC.Applications.CertifiedBurn.Checks.Vp
import GNC.Applications.CertifiedBurn.Checks.Ip
import GNC.Applications.CertifiedBurn.Checks.Mv
import GNC.Applications.CertifiedBurn.Checks.Vv
import GNC.Applications.CertifiedBurn.Checks.Iv

/-! Certified reachable set of a misaligned perigee burn followed by a coast:
two burn steps of `1/16` and thirty-two coast steps of `15/64` of a degree-20
Taylor integrator (normalized units, perigee radius and circular perigee speed
one). Every step's rational certificate is checked by the kernel through
`BurnStep.Valid` (`Steps`), the exact composed transitions are checked pairwise
at every node (`Checks`), and `chain_node_bounds` turns them into position and
velocity bounds of the deviation from the first-order segment `x̂_i + δ ĝ_i` at
every node, for every misalignment `|δ| ≤ α` and every true motion from the
exact start `(1, 0, 0, 21/20)`. The reachable-set readings (segment plus ball,
support function, orbital energy and angular momentum) follow at every node,
and the bounds are rescaled to SI units. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Set Finset Matrix
open GNC.Planning.PolynomialKernel GNC.PolynomialBounds
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn GNC.PlanarCoast GNC.PlanarBurn
open scoped RealInnerProductSpace

/-! ### True motions from the exact start -/

/-- A true motion of the burn and coast chain with misalignment `δ`: one
position and velocity curve per step on the local step time, `Q' = V` and
`V' = g(Q) + f w(t) R(δ) e` on the closed step interval (with `f = 0` on the
coast steps), continuity across the junctions, and the exact start
`(1, 0, 0, 21/20)`. The derivatives are two-sided at the step endpoints and
position, velocity and gravity are continuous on the whole line, so each step
curve is the solution of its own step equation on an open interval around
`[0, h]`, extended continuously beyond it; at the end of the burn the burn
curve continues the burn equation past `h` and the coast curve continues the
coast equation before `0`, both through the common junction state. -/
structure Motion (Q V : ℕ → ℝ → E2) (δ : ℝ) : Prop where
  misalign : |δ| ≤ (Ledger.alpha : ℝ)
  contQ : ∀ j, j ≤ 33 → Continuous (Q j)
  contV : ∀ j, j ≤ 33 → Continuous (V j)
  contField : ∀ j, j ≤ 33 → Continuous (fun s => Gravity.field 1 (Q j s))
  derivQ : ∀ j, j ≤ 33 → ∀ s ∈ Icc (0 : ℝ) ((steps j).bc.h : ℝ), HasDerivAt (Q j) (V j s) s
  derivV : ∀ j, j ≤ 33 → ∀ s ∈ Icc (0 : ℝ) ((steps j).bc.h : ℝ),
    HasDerivAt (V j) (Gravity.field 1 (Q j s) + (steps j).bc.thrustAcc δ s) s
  joinQ : ∀ j, j < 33 → Q (j + 1) 0 = Q j ((steps j).bc.h : ℝ)
  joinV : ∀ j, j < 33 → V (j + 1) 0 = V j ((steps j).bc.h : ℝ)
  startQ : Q 0 0 = pack 1 0
  startV : V 0 0 = pack 0 (21 / 20)

/-- A rational square witness bounds the norm of a plane vector. -/
theorem pack_norm_le_of_sq (a b : ℝ) (B : ℚ) (hB0 : 0 ≤ B) (hsq : a ^ 2 + b ^ 2 ≤ (B : ℝ) ^ 2) :
    ‖pack a b‖ ≤ (B : ℝ) := by
  have hB : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB0
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).mp (by rw [pack_norm_sq]; exact hsq)

/-- The certified node bounds: for every misalignment `|δ| ≤ α` and every true
motion from the exact start, the deviation from the first-order segment at the
end of every step `i` has position norm at most `E^p_i` and velocity norm at
most `E^v_i` (the ledger values, normalized units). -/
theorem orbit_nodes {Q V : ℕ → ℝ → E2} {δ : ℝ} (hm : Motion Q V δ) :
    ∀ i, i ≤ 33 →
      ‖Q i ((steps i).bc.h : ℝ) - (steps i).bc.toCandidate.pos ((steps i).bc.h : ℝ)
          - δ • (steps i).bc.gp ((steps i).bc.h : ℝ)‖ ≤ (Ledger.posBounds.getD i 0 : ℝ)
      ∧ ‖V i ((steps i).bc.h : ℝ) - (steps i).bc.toCandidate.dpos ((steps i).bc.h : ℝ)
          - δ • (steps i).bc.gv ((steps i).bc.h : ℝ)‖ ≤ (Ledger.velBounds.getD i 0 : ℝ) := by
  set Q' : ℕ → ℝ → E2 := fun j => Q (min j 33) with hQ'
  set V' : ℕ → ℝ → E2 := fun j => V (min j 33) with hV'
  have hmin : ∀ j, min j 33 ≤ 33 := fun j => min_le_right _ _
  have hδ : ∀ j, |δ| ≤ ((steps j).bc.alpha : ℝ) := by
    intro j; rw [alpha_eq]; exact hm.misalign
  have h00 : min 0 33 = 0 := by norm_num
  obtain ⟨hgx, hgy, hgvx, hgvy, he0p, hsqp, he0v, hsqv⟩ := init_data
  have hinitp : ‖Q' 0 0 - (steps 0).bc.toCandidate.pos 0 - δ • (steps 0).bc.gp 0‖
      ≤ (Ledger.e0p : ℝ) := by
    simp only [hQ', h00, hm.startQ, Candidate.pos, BurnCandidate.gp, ev_zero, hgx, hgy,
      pack_smul, pack_sub]
    refine pack_norm_le_of_sq _ _ _ he0p ?_
    have := (Rat.cast_le (K := ℝ)).mpr hsqp
    push_cast at this ⊢; linarith
  have hinitv : ‖V' 0 0 - (steps 0).bc.toCandidate.dpos 0 - δ • (steps 0).bc.gv 0‖
      ≤ (Ledger.e0v : ℝ) := by
    simp only [hV', h00, hm.startV, Candidate.dpos, BurnCandidate.gv, ev_zero, hgvx, hgvy,
      pack_smul, pack_sub]
    refine pack_norm_le_of_sq _ _ _ he0v ?_
    have := (Rat.cast_le (K := ℝ)).mpr hsqv
    push_cast at this ⊢; linarith
  have key := chain_node_bounds steps 33 Ledger.e0p Ledger.e0v valid_all Q' V' δ hδ
    (fun j => hm.contQ _ (hmin j)) (fun j => hm.contV _ (hmin j))
    (fun j => hm.contField _ (hmin j))
    (fun j s hs => hm.derivQ _ (hmin j) s (by rw [steps_min]; exact hs))
    (fun j s hs => by
      have := hm.derivV _ (hmin j) s (by rw [steps_min]; exact hs)
      rw [steps_min] at this; exact this)
    (fun j hj => by
      show Q (min (j + 1) 33) 0 = Q (min j 33) _
      rw [min_eq_left (by omega), min_eq_left (by omega)]; exact hm.joinQ j hj)
    (fun j hj => by
      show V (min (j + 1) 33) 0 = V (min j 33) _
      rw [min_eq_left (by omega), min_eq_left (by omega)]; exact hm.joinV j hj)
    hinitp hinitv hEin0 hEinS hjX hjG chkMf chkVf chkIf chkMp chkVp chkIp chkMv chkVv chkIv
  intro i hi
  obtain ⟨_, hp, hv⟩ := key i hi
  have hQi : Q' i = Q i := by simp only [hQ', min_eq_left hi]
  have hVi : V' i = V i := by simp only [hV', min_eq_left hi]
  rw [hQi] at hp; rw [hVi] at hv
  have hpl := pos_ledger i (Finset.mem_range.mpr (by omega))
  have hvl := vel_ledger i (Finset.mem_range.mpr (by omega))
  rw [hpl] at hp; rw [hvl] at hv
  exact ⟨hp, hv⟩

/-! ### Reading the reachable set -/

/-- Segment plus ball: at every node the reachable position lies within `E^p_i`
of the first-order segment `{q̂_i + δ' ĝ_{p,i} : |δ'| ≤ α}`, and likewise the
velocity within `E^v_i` of `{q̂'_i + δ' ĝ_{v,i}}`. -/
theorem reachable_segment_nodes {Q V : ℕ → ℝ → E2} {δ : ℝ} (hm : Motion Q V δ) :
    ∀ i, i ≤ 33 →
      (∃ δ', |δ'| ≤ (Ledger.alpha : ℝ) ∧
        ‖Q i ((steps i).bc.h : ℝ) - (steps i).bc.toCandidate.pos ((steps i).bc.h : ℝ)
          - δ' • (steps i).bc.gp ((steps i).bc.h : ℝ)‖ ≤ (Ledger.posBounds.getD i 0 : ℝ))
      ∧ (∃ δ', |δ'| ≤ (Ledger.alpha : ℝ) ∧
        ‖V i ((steps i).bc.h : ℝ) - (steps i).bc.toCandidate.dpos ((steps i).bc.h : ℝ)
          - δ' • (steps i).bc.gv ((steps i).bc.h : ℝ)‖ ≤ (Ledger.velBounds.getD i 0 : ℝ)) := by
  intro i hi
  obtain ⟨hp, hv⟩ := orbit_nodes hm i hi
  exact ⟨reachable_segment _ _ _ δ _ _ hm.misalign hp, reachable_segment _ _ _ δ _ _ hm.misalign hv⟩

/-- Support function: at every node and in every unit direction `u`, the
reachable position satisfies `u · q ≤ u · q̂_i + α |u · ĝ_{p,i}| + E^p_i`, and
likewise the velocity. -/
theorem reachable_support_nodes {Q V : ℕ → ℝ → E2} {δ : ℝ} (hm : Motion Q V δ)
    (i : ℕ) (hi : i ≤ 33) (u : E2) (hu : ‖u‖ = 1) :
    (inner ℝ u (Q i ((steps i).bc.h : ℝ)) : ℝ)
        ≤ (inner ℝ u ((steps i).bc.toCandidate.pos ((steps i).bc.h : ℝ)) : ℝ)
          + (Ledger.alpha : ℝ) * |(inner ℝ u ((steps i).bc.gp ((steps i).bc.h : ℝ)) : ℝ)|
          + (Ledger.posBounds.getD i 0 : ℝ)
    ∧ (inner ℝ u (V i ((steps i).bc.h : ℝ)) : ℝ)
        ≤ (inner ℝ u ((steps i).bc.toCandidate.dpos ((steps i).bc.h : ℝ)) : ℝ)
          + (Ledger.alpha : ℝ) * |(inner ℝ u ((steps i).bc.gv ((steps i).bc.h : ℝ)) : ℝ)|
          + (Ledger.velBounds.getD i 0 : ℝ) := by
  obtain ⟨hp, hv⟩ := orbit_nodes hm i hi
  exact ⟨reachable_support _ _ _ u δ _ _ hu hm.misalign hp,
    reachable_support _ _ _ u δ _ _ hu hm.misalign hv⟩

/-- The orbital enclosure of the reachable states at node `i`: the specific
energy and planar angular momentum of the true state differ from the nominal by
the enclosure bounds at `P = α Gp + E^p_i` and `W = α Gv + E^v_i`. -/
def EnclosureAt (Q V : ℕ → ℝ → E2) (i : ℕ) : Prop :=
  let ph := (steps i).bc.toCandidate.pos ((steps i).bc.h : ℝ)
  let vh := (steps i).bc.toCandidate.dpos ((steps i).bc.h : ℝ)
  let P := (Ledger.alpha : ℝ) * ((steps i).bc.Gp : ℝ) + (Ledger.posBounds.getD i 0 : ℝ)
  let W := (Ledger.alpha : ℝ) * ((steps i).bc.Gv : ℝ) + (Ledger.velBounds.getD i 0 : ℝ)
  |GNC.OrbitalEnergy.specificEnergy 1 (Q i ((steps i).bc.h : ℝ)) (V i ((steps i).bc.h : ℝ))
      - GNC.OrbitalEnergy.specificEnergy 1 ph vh|
      ≤ ‖vh‖ * W + W ^ 2 / 2 + P / (‖ph‖ * (‖ph‖ - P))
    ∧ |planarMom (Q i ((steps i).bc.h : ℝ)) (V i ((steps i).bc.h : ℝ)) - planarMom ph vh|
      ≤ ‖ph‖ * W + P * ‖vh‖ + P * W

/-- Orbital enclosure at a node whose segment and ball stay inside the radius
floor. -/
theorem orbit_enclosure_node {Q V : ℕ → ℝ → E2} {δ : ℝ} (hm : Motion Q V δ)
    (i : ℕ) (hi : i ≤ 33)
    (hsmall : Ledger.alpha * (steps i).bc.Gp + Ledger.posBounds.getD i 0 < (steps i).bc.rhoMin) :
    EnclosureAt Q V i := by
  unfold EnclosureAt
  intro ph vh P W
  obtain ⟨hp, hv⟩ := orbit_nodes hm i hi
  have hv' := valid_all i
  have hh0 : (0 : ℝ) ≤ ((steps i).bc.h : ℝ) := by exact_mod_cast hv'.1.1.1
  have hend : ((steps i).bc.h : ℝ) ∈ Icc (0 : ℝ) ((steps i).bc.h : ℝ) := right_mem_Icc.mpr hh0
  have hgp := BurnCandidate.Gp_sound (steps i).bc hend
  have hgv := BurnCandidate.Gv_sound (steps i).bc hend
  have hrho : ((steps i).bc.rhoMin : ℝ) ≤ ‖ph‖ :=
    (steps i).bc.toCandidate.rhoMin_le_norm_pos hv'.1.1 hend
  have hsm : (Ledger.alpha : ℝ) * ((steps i).bc.Gp : ℝ) + (Ledger.posBounds.getD i 0 : ℝ) < ‖ph‖ := by
    have := (Rat.cast_lt (K := ℝ)).mpr hsmall
    push_cast at this; linarith
  exact reachable_orbit_enclosure ph vh _ _ _ _ hm.misalign hgp hgv hp hv hsm

/-- The segment and ball at the burn-end node stay inside its radius floor. -/
theorem small_burnEnd :
    Ledger.alpha * (steps Ledger.burnEnd).bc.Gp + Ledger.posBounds.getD Ledger.burnEnd 0
      < (steps Ledger.burnEnd).bc.rhoMin := by decide +kernel

/-- The segment and ball at the final node stay inside its radius floor. -/
theorem small_last :
    Ledger.alpha * (steps Ledger.last).bc.Gp + Ledger.posBounds.getD Ledger.last 0
      < (steps Ledger.last).bc.rhoMin := by decide +kernel

theorem burnEnd_le : Ledger.burnEnd ≤ 33 := by decide
theorem last_le : Ledger.last ≤ 33 := by decide

/-- Orbital enclosure of the reachable set at the end of the burn. -/
theorem orbit_enclosure_burnEnd {Q V : ℕ → ℝ → E2} {δ : ℝ} (hm : Motion Q V δ) :
    EnclosureAt Q V Ledger.burnEnd :=
  orbit_enclosure_node hm Ledger.burnEnd burnEnd_le small_burnEnd

/-- Orbital enclosure of the reachable set at the end of the coast. -/
theorem orbit_enclosure_last {Q V : ℕ → ℝ → E2} {δ : ℝ} (hm : Motion Q V δ) :
    EnclosureAt Q V Ledger.last :=
  orbit_enclosure_node hm Ledger.last last_le small_last

/-! ### Physical (SI) rescaling -/

/-- Metres per normalized length unit (perigee radius). -/
def radiusSI : ℚ := 7000000
/-- Metres per second per normalized velocity unit, the rational upper bound
`7546.4 m/s` of the circular perigee speed `sqrt(mu/r_p) ≈ 7546.05 m/s`
(`mu = 3.986004418e14 m³/s²`, `r_p = 7000 km`). -/
def speedSI : ℚ := 75464 / 10

/-- Node bounds in SI units: position deviation in metres and velocity
deviation in metres per second, at the end of every step. -/
theorem physical_bounds_SI {Q V : ℕ → ℝ → E2} {δ : ℝ} (hm : Motion Q V δ) :
    ∀ i, i ≤ 33 →
      (radiusSI : ℝ) * ‖Q i ((steps i).bc.h : ℝ) - (steps i).bc.toCandidate.pos ((steps i).bc.h : ℝ)
          - δ • (steps i).bc.gp ((steps i).bc.h : ℝ)‖
        ≤ ((radiusSI * Ledger.posBounds.getD i 0 : ℚ) : ℝ)
      ∧ (speedSI : ℝ) * ‖V i ((steps i).bc.h : ℝ) - (steps i).bc.toCandidate.dpos ((steps i).bc.h : ℝ)
          - δ • (steps i).bc.gv ((steps i).bc.h : ℝ)‖
        ≤ ((speedSI * Ledger.velBounds.getD i 0 : ℚ) : ℝ) := by
  intro i hi
  obtain ⟨hp, hv⟩ := orbit_nodes hm i hi
  refine ⟨?_, ?_⟩
  · rw [show ((radiusSI * Ledger.posBounds.getD i 0 : ℚ) : ℝ)
        = (radiusSI : ℝ) * (Ledger.posBounds.getD i 0 : ℝ) by push_cast; ring]
    exact mul_le_mul_of_nonneg_left hp (by norm_num [radiusSI])
  · rw [show ((speedSI * Ledger.velBounds.getD i 0 : ℚ) : ℝ)
        = (speedSI : ℝ) * (Ledger.velBounds.getD i 0 : ℝ) by push_cast; ring]
    exact mul_le_mul_of_nonneg_left hv (by norm_num [speedSI])

end GNC.Applications.CertifiedBurn.Orbit
