import GNC.Applications.OrbitalFuel.TerminalGravityData
import GNC.Applications.OrbitalFuel.TerminalGravityTheory

/-! All-time integral certificates for the six terminal transport rows.
All polynomial cells, row errors, Young parameters and accumulated budgets
are checked. The actual input is the validated time-varying trajectory.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.TerminalGravity
open GNC PolynomialBurn

theorem norm_integral (x : Trajectory) (i : Fin 6) :
    (∫ t in (0:ℝ)..(3/5), GNC.enorm (kernel x i t)) ≤ (gain i:ℝ) := by
  have hc : Continuous (fun t => GNC.enorm (kernel x i t)) :=
    (ThrustSupport.euclideanEquiv.continuous.comp (kernel_continuous x i)).norm
  have hj := intervalIntegral.sum_integral_adjacent_intervals
    (μ := MeasureTheory.volume)
    (a := fun k : ℕ => (k:ℝ)*(3/160)) (n := 32)
    (fun k _ => hc.intervalIntegrable ((k:ℝ)*(3/160)) (((k+1:ℕ):ℝ)*(3/160)))
  have he : (∫ t in (0:ℝ)..(3/5), GNC.enorm (kernel x i t)) =
      ∑ j : Fin 32, ∫ t in ((j.val:ℝ)*(3/160))..((j.val:ℝ)*(3/160)+3/160),
        GNC.enorm (kernel x i t) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ∫ t in ((j:ℝ)*(3/160))..((j:ℝ)*(3/160)+3/160), GNC.enorm (kernel x i t)) 32]
    simpa only [Nat.cast_zero, zero_mul, Nat.cast_ofNat, show (32:ℝ)*(3/160) = 3/5 by norm_num,
      Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hj.symm
  rw [he]
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin 32) _ =>
    (cell_norm_bound x j i (cell_certificate j i).1).trans
      (show (youngIntegral j i (nu j i):ℝ) ≤ (budget j i:ℝ) by
        exact_mod_cast (cell_certificate j i).2))
  have hg : (∑ j : Fin 32, (budget j i:ℝ)) ≤ (gain i:ℝ) := by
    exact_mod_cast gain_budget i
  exact hb.trans hg

end GNC.Applications.OrbitalFuel.TerminalGravity
