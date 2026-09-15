import GNC.Applications.OrbitalFuel.BurnFormula
import GNC.Applications.OrbitalFuel.ValidatedTransition

/-! Continuous burn-integral enclosures from the checked solar ODE cells.
The trajectory hypotheses are the actual joint differential equation and
initial enclosure. No burn-integral accuracy is assumed.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.PolynomialBurn
open GNC.PolynomialODE GNC.PolynomialOrbitTransition GNC.PolynomialIntegral
open PolynomialTransition

structure Trajectory where
  state : ℝ → Fin 25 → ℝ
  continuous : Continuous state
  derivative : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
    HasDerivAt state (fun i => (field alpha i).value (state t)) t
  initial : ∀ i, |state 0 i-curve (ValidatedTransition.sequence 0).coefficients 0 i| ≤
    ((ValidatedTransition.sequence 0).initialError i:ℝ)

def Trajectory.ofFlow (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hdz : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt z (GNC.PolynomialOrbit.rate alpha (z t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t) * F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t) * H t) t)
    (hiz : z 0 = ValidatedReference.initial) (hiF : F 0 = 1) (hiH : H 0 = 1) : Trajectory where
  state t := pack (z t) (F t) (H t)
  continuous := pack_continuous hz hF hH
  derivative t ht := joint_derivative alpha (hdz t ht) (hdF t ht) (hdH t ht)
  initial := by
    change ∀ i, |pack (z 0) (F 0) (H 0) i-curve (ValidatedTransition.sequence 0).coefficients 0 i| ≤ _
    rw [hiz,hiF,hiH]
    exact ValidatedTransition.initial_error

theorem Trajectory.cell_error (x : Trajectory) (j : Fin 32) {u : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) (3/160)) (i : Fin 25) :
    |x.state ((j.val:ℝ)*(3/160)+u) i-curve (steps j).coefficients u i| < ((steps j).error i:ℝ) := by
  have h := box_chain_sound ValidatedTransition.sequence (field alpha) 32 (3/160)
    ValidatedTransition.sequence_valid ValidatedTransition.sequence_duration ValidatedTransition.sequence_join x.state x.continuous
    (fun t ht => x.derivative t (by norm_num at ht ⊢; exact ht)) x.initial
  simpa [ValidatedTransition.sequence, j.isLt] using h j.val j.isLt u (by norm_num at hu ⊢; exact hu) i

def observationIntegral (c : Cell) (e : Expr 25) : ℚ :=
  integrate (e.coefficients (steps c.step).coefficients) c.lower c.upper

def observationMean (cells : Fin 3 → Cell) (e : Expr 25) : ℚ :=
  50 * ∑ k : Fin 3, observationIntegral (cells k) e

theorem Trajectory.observable_cell_integral (x : Trajectory) (c : Cell) (hc : c.Valid) (e : Expr 25) (ε : ℚ)
    (herr : ∀ j, e.differenceMajorant (steps j).region (steps j).error ≤ ε) :
    |(∫ t in (c.start:ℝ)..(c.finish:ℝ), e.value (x.state t)) -
      ((observationIntegral c e:ℚ):ℝ)| ≤ (((c.upper-c.lower)*(ε):ℚ):ℝ) := by
  have hi := (steps c.step).observable_integral_shifted (steps_valid c.step)
    x.state x.continuous e (c.step.val*(3/160)) hc.1 hc.2.1
    (by rw [durations]; exact hc.2.2)
    (fun t ht i => by
      have hupper : (c.upper:ℝ) ≤ 3/160 := by
        have hcast := (Rat.cast_le (K := ℝ)).mpr hc.2.2
        norm_num at hcast ⊢
        exact hcast
      have hu : t ∈ Set.Icc (0:ℝ) (3/160) :=
        ⟨le_trans (by exact_mod_cast hc.1) ht.1, le_trans ht.2 hupper⟩
      simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] using
        (x.cell_error c.step hu i).le)
  have he : (c.upper-c.lower)*e.differenceMajorant (steps c.step).region
      (steps c.step).error ≤ (c.upper-c.lower)*(ε) :=
    mul_le_mul_of_nonneg_left (herr c.step) (sub_nonneg.mpr hc.2.1)
  exact hi.trans (by exact_mod_cast he)

theorem Trajectory.cell_integral (x : Trajectory) (c : Cell) (hc : c.Valid) (o : Fin 10) :
    |(∫ t in (c.start:ℝ)..(c.finish:ℝ), (observable o).value (x.state t)) -
      ((cellIntegral c o:ℚ):ℝ)| ≤ (((c.upper-c.lower)*(1/10^14):ℚ):ℝ) :=
  x.observable_cell_integral c hc (observable o) (1/10^14) (fun j => observation_errors j o)

def times (cells : Fin 3 → Cell) : ℕ → ℚ
  | 0 => (cells 0).start
  | 1 => (cells 1).start
  | 2 => (cells 2).start
  | _ => (cells 2).finish

theorem times_start (cells : Fin 3 → Cell) (k : Fin 3) : times cells k.val = (cells k).start := by
  fin_cases k <;> rfl

theorem times_finish (cells : Fin 3 → Cell)
    (hj : ∀ k : Fin 2, (cells k.castSucc).finish = (cells k.succ).start) (k : Fin 3) :
    times cells (k.val+1) = (cells k).finish := by
  fin_cases k
  · exact (hj 0).symm
  · exact (hj 1).symm
  · rfl

theorem Trajectory.observable_mean_error (x : Trajectory) (cells : Fin 3 → Cell) (e : Expr 25) (ε : ℚ)
    (herr : ∀ j, e.differenceMajorant (steps j).region (steps j).error ≤ ε)
    (hc : ∀ k, (cells k).Valid)
    (hj : ∀ k : Fin 2, (cells k.castSucc).finish = (cells k.succ).start)
    (hd : (cells 2).finish-(cells 0).start = 1/50) :
    |50*(∫ t in ((cells 0).start:ℝ)..((cells 2).finish:ℝ), e.value (x.state t)) -
      ((observationMean cells e:ℚ):ℝ)| ≤ ((ε:ℝ):ℝ) := by
  let values : ℕ → ℝ := fun k => if hk : k < 3 then (observationIntegral (cells ⟨k,hk⟩) e:ℚ) else 0
  have he := GNC.IntegralPartition.uniform_error (fun t => e.value (x.state t))
    (fun k => (times cells k:ℝ)) values 3 ((ε:ℝ))
    (fun k _ => (e.value_continuous x.continuous).intervalIntegrable _ _)
    (fun k hk => by
      have h := x.observable_cell_integral (cells ⟨k,hk⟩) (hc ⟨k,hk⟩) e ε herr
      dsimp only
      rw [times_start cells ⟨k,hk⟩, times_finish cells hj ⟨k,hk⟩]
      have hlen : (cells ⟨k,hk⟩).finish-(cells ⟨k,hk⟩).start =
          (cells ⟨k,hk⟩).upper-(cells ⟨k,hk⟩).lower := by
        simp only [Cell.start, Cell.finish]; ring
      have hlenR : ((cells ⟨k,hk⟩).finish:ℝ)-((cells ⟨k,hk⟩).start:ℝ) =
          ((cells ⟨k,hk⟩).upper:ℝ)-((cells ⟨k,hk⟩).lower:ℝ) := by exact_mod_cast hlen
      simpa only [values, dif_pos hk, hlenR, Rat.cast_mul, Rat.cast_sub, Rat.cast_div,
        Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using h)
  have hv : (∑ k ∈ Finset.range 3, values k) =
      ((∑ k : Fin 3, observationIntegral (cells k) e:ℚ):ℝ) := by
    norm_num [values, Fin.sum_univ_succ, Finset.sum_range_succ]
    change (observationIntegral (cells 0) e:ℝ)+(observationIntegral (cells 1) e:ℝ)+(observationIntegral (cells 2) e:ℝ) =
      (observationIntegral (cells 0) e:ℝ)+((observationIntegral (cells 1) e:ℝ)+(observationIntegral (cells 2) e:ℝ))
    ring
  rw [hv] at he
  change |(∫ t in ((cells 0).start:ℝ)..((cells 2).finish:ℝ), e.value (x.state t)) -
    ((∑ k : Fin 3, observationIntegral (cells k) e:ℚ):ℝ)| ≤ _ at he
  have hlen : ((cells 2).finish:ℝ)-((cells 0).start:ℝ) = 1/50 := by
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using congrArg (fun q : ℚ => (q:ℝ)) hd
  change |50*(∫ t in ((cells 0).start:ℝ)..((cells 2).finish:ℝ), e.value (x.state t)) -
    ((50*(∑ k : Fin 3, observationIntegral (cells k) e):ℚ):ℝ)| ≤ _
  rw [Rat.cast_mul, Rat.cast_ofNat, ← mul_sub, abs_mul]
  rw [abs_of_pos (by norm_num : (0:ℝ) < 50)]
  change _ ≤ (((cells 2).finish:ℝ)-((cells 0).start:ℝ))*((ε:ℝ)) at he
  rw [hlen] at he
  linarith

theorem Trajectory.mean_error (x : Trajectory) (cells : Fin 3 → Cell) (o : Fin 10)
    (hc : ∀ k, (cells k).Valid)
    (hj : ∀ k : Fin 2, (cells k.castSucc).finish = (cells k.succ).start)
    (hd : (cells 2).finish-(cells 0).start = 1/50) :
    |50*(∫ t in ((cells 0).start:ℝ)..((cells 2).finish:ℝ), (observable o).value (x.state t)) -
      ((mean cells o:ℚ):ℝ)| ≤ (1/10^14:ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
    x.observable_mean_error cells (observable o) (1/10^14) (fun j => observation_errors j o) hc hj hd

theorem Trajectory.rounded_mean (x : Trajectory) (cells : Fin 3 → Cell) (o : Fin 10) (center : ℚ)
    (hc : ∀ k, (cells k).Valid)
    (hj : ∀ k : Fin 2, (cells k.castSucc).finish = (cells k.succ).start)
    (hd : (cells 2).finish-(cells 0).start = 1/50)
    (hr : |mean cells o-center| ≤ 1/10^25) :
    |50*(∫ t in ((cells 0).start:ℝ)..((cells 2).finish:ℝ), (observable o).value (x.state t)) -
      (center:ℝ)| ≤ 2/10^14 := by
  have h := x.mean_error cells o hc hj hd
  have hr' : |(mean cells o:ℝ)-(center:ℝ)| ≤ (1/10^25:ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hr
    norm_num at hcast ⊢
    exact hcast
  have ht := abs_sub_le
    (50*(∫ t in ((cells 0).start:ℝ)..((cells 2).finish:ℝ), (observable o).value (x.state t)))
    (mean cells o:ℝ) (center:ℝ)
  linarith

end GNC.Applications.OrbitalFuel.PolynomialBurn
