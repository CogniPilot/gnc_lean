import GNC.Applications.CertifiedCoast.Step

/-! Composition of certified coast steps into a whole-orbit error bound. A
chain of `Step`s is compatible when each terminal radius plus the rational
handoff mismatch between consecutive candidate polynomials dominates the next
initial radius. `chain_sound` transports the per-step envelopes of
`InitialPolynomialSupersolution.chain_envelope` to the true inverse-square
trajectory, `chain_terminal` reads off the certified terminal radii, and
`physical_bounds_SI` rescales them to metres and metres per second. -/
noncomputable section
namespace GNC.CertifiedCoast
open Set GNC.PlanarCoast GNC.PlanarCoast.Candidate GNC.InitialPolynomialSupersolution
  GNC.Planning.PolynomialKernel

/-! ### Real evaluation of a rational coefficient list at a rational point -/

theorem ev_ratEval (cs : List ℚ) (t : ℚ) : ev cs (t:ℝ) = ((evaluate cs t : ℚ):ℝ) := by
  rw [ev]
  have := evaluate_map (Rat.castHom ℝ) cs t
  simpa using this

/-! ### Handoff mismatch between two candidate polynomials -/

/-- Position handoff mismatch: the sum of the coordinate discrepancies of the
first candidate at its endpoint and the second candidate at its start. -/
def cposMismatch (a b : Candidate) : ℚ :=
  |evaluate a.x a.h-evaluate b.x 0|+|evaluate a.y a.h-evaluate b.y 0|

/-- Velocity handoff mismatch, using the derivative coefficient lists. -/
def cvelMismatch (a b : Candidate) : ℚ :=
  |evaluate (differentiate a.x) a.h-evaluate (differentiate b.x) 0|+
    |evaluate (differentiate a.y) a.h-evaluate (differentiate b.y) 0|

theorem cpos_mismatch_bound (a b : Candidate) :
    ‖a.pos (a.h:ℝ)-b.pos 0‖ ≤ ((cposMismatch a b:ℚ):ℝ) := by
  have hx : ev a.x (a.h:ℝ)-ev b.x 0 = ((evaluate a.x a.h-evaluate b.x 0 : ℚ):ℝ) := by
    rw [ev_ratEval a.x a.h, show (0:ℝ) = ((0:ℚ):ℝ) from by norm_num, ev_ratEval b.x 0]
    push_cast; ring
  have hy : ev a.y (a.h:ℝ)-ev b.y 0 = ((evaluate a.y a.h-evaluate b.y 0 : ℚ):ℝ) := by
    rw [ev_ratEval a.y a.h, show (0:ℝ) = ((0:ℚ):ℝ) from by norm_num, ev_ratEval b.y 0]
    push_cast; ring
  rw [Candidate.pos, Candidate.pos, pack_sub]
  refine (pack_norm_le _ _).trans (le_of_eq ?_)
  rw [hx, hy, cposMismatch]; push_cast; ring

theorem cvel_mismatch_bound (a b : Candidate) :
    ‖a.dpos (a.h:ℝ)-b.dpos 0‖ ≤ ((cvelMismatch a b:ℚ):ℝ) := by
  have hx : ev (differentiate a.x) (a.h:ℝ)-ev (differentiate b.x) 0 =
      ((evaluate (differentiate a.x) a.h-evaluate (differentiate b.x) 0 : ℚ):ℝ) := by
    rw [ev_ratEval (differentiate a.x) a.h, show (0:ℝ) = ((0:ℚ):ℝ) from by norm_num,
      ev_ratEval (differentiate b.x) 0]
    push_cast; ring
  have hy : ev (differentiate a.y) (a.h:ℝ)-ev (differentiate b.y) 0 =
      ((evaluate (differentiate a.y) a.h-evaluate (differentiate b.y) 0 : ℚ):ℝ) := by
    rw [ev_ratEval (differentiate a.y) a.h, show (0:ℝ) = ((0:ℚ):ℝ) from by norm_num,
      ev_ratEval (differentiate b.y) 0]
    push_cast; ring
  rw [Candidate.dpos, Candidate.dpos, pack_sub]
  refine (pack_norm_le _ _).trans (le_of_eq ?_)
  rw [hx, hy, cvelMismatch]; push_cast; ring

/-- Two consecutive steps are compatible when each terminal radius plus the
candidate handoff mismatch is dominated by the next initial radius. -/
def Step.Compatible (s next : Step) : Prop :=
  cposMismatch s.c next.c+s.rpEnd ≤ next.rp ∧ cvelMismatch s.c next.c+s.rvEnd ≤ next.rv

instance (s next : Step) : Decidable (s.Compatible next) := by
  unfold Step.Compatible; infer_instance

/-! ### Continuity of the packed true trajectory -/

theorem truePos_continuous {w : ℝ → Fin 4 → ℝ} (hwc : Continuous w) :
    Continuous (truePos w) := by
  have h0 : Continuous (fun t => w t 0) := (continuous_apply 0).comp hwc
  have h1 : Continuous (fun t => w t 1) := (continuous_apply 1).comp hwc
  have hpi : Continuous (fun t => (![w t 0, w t 1] : Fin 2 → ℝ)) := by
    apply continuous_pi; intro i; fin_cases i <;> simpa
  exact ((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.continuous).comp hpi

theorem trueVel_continuous {w : ℝ → Fin 4 → ℝ} (hwc : Continuous w) :
    Continuous (trueVel w) := by
  have h2 : Continuous (fun t => w t 2) := (continuous_apply 2).comp hwc
  have h3 : Continuous (fun t => w t 3) := (continuous_apply 3).comp hwc
  have hpi : Continuous (fun t => (![w t 2, w t 3] : Fin 2 → ℝ)) := by
    apply continuous_pi; intro i; fin_cases i <;> simpa
  exact ((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.continuous).comp hpi

/-! ### Soundness of the chain -/

/-- Every true inverse-square solution of the chain stays inside the per-step
envelope, provided every step is valid and every handoff is compatible. -/
theorem chain_sound (S : ℕ → Step) (N : ℕ)
    (hv : ∀ j < N, (S j).Valid)
    (hc : ∀ j, j+1 < N → (S j).Compatible (S (j+1)))
    (w : ℕ → ℝ → Fin 4 → ℝ)
    (hwc : ∀ j < N, Continuous (w j))
    (hw : ∀ j < N, ∀ t ∈ Icc (0:ℝ) ((S j).c.h:ℝ),
      HasDerivAt (w j) (PolynomialOrbit.physicalRate 0 (w j t)) t)
    (hjoin : ∀ j, j+1 < N → w (j+1) 0 = w j ((S j).c.h:ℝ))
    (hp0 : ‖truePos (w 0) 0-(S 0).c.pos 0‖ ≤ ((S 0).rp:ℝ))
    (hv0 : ‖trueVel (w 0) 0-(S 0).c.dpos 0‖ ≤ ((S 0).rv:ℝ)) :
    ∀ j < N, ∀ t ∈ Icc (0:ℝ) ((S j).c.h:ℝ),
      ‖truePos (w j) t-(S j).c.pos t‖ ≤ (S j).envR (t/((S j).c.h:ℝ)) ∧
        ‖trueVel (w j) t-(S j).c.dpos t‖ ≤ (S j).envVR (t/((S j).c.h:ℝ))/((S j).c.h:ℝ) := by
  refine chain_envelope
    (fun j => ((S j).c.h:ℝ)) (fun j => 2/(((S j).c.rhoMin:ℝ)-((S j).M:ℝ))^3)
    (fun j => ((S j).c.defect:ℝ)) (fun j => ((S j).rp:ℝ)) (fun j => ((S j).rv:ℝ))
    (fun j => ((S j).M:ℝ)) (fun j => ((cposMismatch (S j).c (S (j+1)).c:ℚ):ℝ))
    (fun j => ((cvelMismatch (S j).c (S (j+1)).c:ℚ):ℝ))
    (fun j t => truePos (w j) t-(S j).c.pos t)
    (fun j t => trueVel (w j) t-(S j).c.dpos t)
    (fun j t => Gravity.field 1 (truePos (w j) t)-(S j).c.acc t)
    (fun j _ => ((S j).c.defect:ℝ))
    ?hT ?hkappa ?hF ?hk ?hclose ?hpc ?hvc ?hdp ?hdv ?hf ?ha hp0 hv0 ?hd ?he ?hrp ?hrv
  case hT =>
    intro j hj; show (0:ℝ) < ((S j).c.h:ℝ); exact_mod_cast (hv j hj).2.1
  case hkappa =>
    intro j hj
    have hx : (0:ℝ) < ((S j).c.rhoMin:ℝ)-((S j).M:ℝ) := by
      have := Step.M_lt_rhoMin (S j) (hv j hj); linarith
    exact le_of_lt (div_pos (by norm_num) (pow_pos hx 3))
  case hF => exact fun j hj => Step.defect_nonneg (S j).c (hv j hj).1
  case hk => exact fun j hj => Step.kR_lt_56 (S j) (hv j hj)
  case hclose => exact fun j hj => Step.close (S j) (hv j hj)
  case hpc => exact fun j hj => (truePos_continuous (hwc j hj)).sub (S j).c.pos_continuous
  case hvc => exact fun j hj => (trueVel_continuous (hwc j hj)).sub (S j).c.dpos_continuous
  case hdp => exact fun j hj t ht => errorPos_hasDerivAt (S j).c (hw j hj t ht)
  case hdv => exact fun j hj t ht => errorVel_hasDerivAt (S j).c (hw j hj t ht)
  case hf => exact fun j hj t ht => le_rfl
  case ha =>
    exact fun j hj t ht hp =>
      Step.acceleration_hypothesis_defect (S j).c (hv j hj).1 ht
        (Step.M_lt_rhoMin (S j) (hv j hj)) (w j) hp
  case hd =>
    intro j hj
    have htp : truePos (w (j+1)) 0 = truePos (w j) ((S j).c.h:ℝ) := by
      simp only [truePos, hjoin j hj]
    refine le_of_eq_of_le ?_ (cpos_mismatch_bound (S j).c (S (j+1)).c)
    congr 1
    show (truePos (w (j+1)) 0-(S (j+1)).c.pos 0)-
        (truePos (w j) ((S j).c.h:ℝ)-(S j).c.pos ((S j).c.h:ℝ)) =
      (S j).c.pos ((S j).c.h:ℝ)-(S (j+1)).c.pos 0
    rw [htp]; abel
  case he =>
    intro j hj
    have htv : trueVel (w (j+1)) 0 = trueVel (w j) ((S j).c.h:ℝ) := by
      simp only [trueVel, hjoin j hj]
    refine le_of_eq_of_le ?_ (cvel_mismatch_bound (S j).c (S (j+1)).c)
    congr 1
    show (trueVel (w (j+1)) 0-(S (j+1)).c.dpos 0)-
        (trueVel (w j) ((S j).c.h:ℝ)-(S j).c.dpos ((S j).c.h:ℝ)) =
      (S j).c.dpos ((S j).c.h:ℝ)-(S (j+1)).c.dpos 0
    rw [htv]; abel
  case hrp =>
    intro j hj
    have h1 : (S j).envR 1 ≤ ((S j).rpEnd:ℝ) := Step.one_le_rpEnd (S j) (hv j (by omega))
    have h2 : ((cposMismatch (S j).c (S (j+1)).c:ℚ):ℝ)+((S j).rpEnd:ℝ) ≤ ((S (j+1)).rp:ℝ) := by
      exact_mod_cast (hc j hj).1
    show (S j).envR 1+((cposMismatch (S j).c (S (j+1)).c:ℚ):ℝ) ≤ ((S (j+1)).rp:ℝ)
    linarith
  case hrv =>
    intro j hj
    have h1 : (S j).envVR 1/((S j).c.h:ℝ) ≤ ((S j).rvEnd:ℝ) := Step.one_le_rvEnd (S j) (hv j (by omega))
    have h2 : ((cvelMismatch (S j).c (S (j+1)).c:ℚ):ℝ)+((S j).rvEnd:ℝ) ≤ ((S (j+1)).rv:ℝ) := by
      exact_mod_cast (hc j hj).2
    show (S j).envVR 1/((S j).c.h:ℝ)+((cvelMismatch (S j).c (S (j+1)).c:ℚ):ℝ) ≤ ((S (j+1)).rv:ℝ)
    linarith

/-- The terminal position and velocity errors of the last of `n+1` chained
steps are at most its certified rational terminal radii. -/
theorem chain_terminal (S : ℕ → Step) (n : ℕ)
    (hv : ∀ j < n+1, (S j).Valid)
    (hc : ∀ j, j+1 < n+1 → (S j).Compatible (S (j+1)))
    (w : ℕ → ℝ → Fin 4 → ℝ)
    (hwc : ∀ j < n+1, Continuous (w j))
    (hw : ∀ j < n+1, ∀ t ∈ Icc (0:ℝ) ((S j).c.h:ℝ),
      HasDerivAt (w j) (PolynomialOrbit.physicalRate 0 (w j t)) t)
    (hjoin : ∀ j, j+1 < n+1 → w (j+1) 0 = w j ((S j).c.h:ℝ))
    (hp0 : ‖truePos (w 0) 0-(S 0).c.pos 0‖ ≤ ((S 0).rp:ℝ))
    (hv0 : ‖trueVel (w 0) 0-(S 0).c.dpos 0‖ ≤ ((S 0).rv:ℝ)) :
    ‖truePos (w n) ((S n).c.h:ℝ)-(S n).c.pos ((S n).c.h:ℝ)‖ ≤ ((S n).rpEnd:ℝ) ∧
      ‖trueVel (w n) ((S n).c.h:ℝ)-(S n).c.dpos ((S n).c.h:ℝ)‖ ≤ ((S n).rvEnd:ℝ) := by
  have hh0 : (0:ℝ) < ((S n).c.h:ℝ) := by exact_mod_cast (hv n (by omega)).2.1
  obtain ⟨hp, hvv⟩ := chain_sound S (n+1) hv hc w hwc hw hjoin hp0 hv0 n (by omega)
    ((S n).c.h:ℝ) ⟨hh0.le, le_rfl⟩
  rw [div_self hh0.ne'] at hp hvv
  exact ⟨hp.trans (Step.one_le_rpEnd (S n) (hv n (by omega))),
    hvv.trans (Step.one_le_rvEnd (S n) (hv n (by omega)))⟩

/-! ### Physical rescaling -/

/-- Metres per normalized length unit (perigee radius). -/
def radiusSI : ℚ := 7000000
/-- Metres per second per normalized velocity unit, a rational upper bound of
`sqrt(mu/r_p) = 7546.36 m/s`. -/
def speedSI : ℚ := 75464/10

/-- The terminal errors of the last chained step in SI units. -/
theorem physical_bounds_SI (S : ℕ → Step) (n : ℕ)
    (hv : ∀ j < n+1, (S j).Valid)
    (hc : ∀ j, j+1 < n+1 → (S j).Compatible (S (j+1)))
    (w : ℕ → ℝ → Fin 4 → ℝ)
    (hwc : ∀ j < n+1, Continuous (w j))
    (hw : ∀ j < n+1, ∀ t ∈ Icc (0:ℝ) ((S j).c.h:ℝ),
      HasDerivAt (w j) (PolynomialOrbit.physicalRate 0 (w j t)) t)
    (hjoin : ∀ j, j+1 < n+1 → w (j+1) 0 = w j ((S j).c.h:ℝ))
    (hp0 : ‖truePos (w 0) 0-(S 0).c.pos 0‖ ≤ ((S 0).rp:ℝ))
    (hv0 : ‖trueVel (w 0) 0-(S 0).c.dpos 0‖ ≤ ((S 0).rv:ℝ)) :
    (radiusSI:ℝ)*‖truePos (w n) ((S n).c.h:ℝ)-(S n).c.pos ((S n).c.h:ℝ)‖ ≤
        (radiusSI:ℝ)*((S n).rpEnd:ℝ) ∧
      (speedSI:ℝ)*‖trueVel (w n) ((S n).c.h:ℝ)-(S n).c.dpos ((S n).c.h:ℝ)‖ ≤
        (speedSI:ℝ)*((S n).rvEnd:ℝ) := by
  obtain ⟨hp, hvv⟩ := chain_terminal S n hv hc w hwc hw hjoin hp0 hv0
  exact ⟨mul_le_mul_of_nonneg_left hp (by norm_num [radiusSI]),
    mul_le_mul_of_nonneg_left hvv (by norm_num [speedSI])⟩

end GNC.CertifiedCoast
