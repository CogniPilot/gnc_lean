import GNC.Applications.OrbitalFuel.RetainedOverlayData
import GNC.Applications.OrbitalFuel.ValidatedRetainedPrefix
import GNC.Analysis.IntegralPrefix

/-! The accumulated polynomial-response representation uses exactly the
original switched forcing integrals, for every time including partial burns.
The extra polynomial-cell boundaries cancel by a checked finite identity.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedOverlay
open GNC ValidatedRetainedPrefix RetainedPrefix PolynomialBurn RetainedOverlayData
set_option autoImplicit false

theorem node_monotone : Monotone node := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < 68
  · exact node_order n hn
  · simp only [node,if_neg hn,if_neg (show ¬n+1 < 68 by omega),le_refl]

theorem node_eq (n : Fin 69) : node n.val = (nodes n:ℝ) := by
  have h := RetainedOverlayData.node_matches n
  by_cases hn : n.val < 68
  · rw [dif_pos hn] at h
    have hc := congrArg (fun q : ℚ => (q:ℝ)) h
    simpa only [node,if_pos hn,normPiece,slot_small n.val hn] using hc
  · rw [dif_neg hn] at h
    have hc := congrArg (fun q : ℚ => (q:ℝ)) h
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hc
    simpa only [node,if_neg hn] using hc

theorem refinement {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Fin 37 → ℝ → E) (hf : ∀ k, Continuous (f k)) (T : ℝ) :
    (∑ i : Fin 68, ∫ t in min (nodes i.castSucc:ℝ) T..min (nodes i.succ:ℝ) T, f (arcs i) t) =
      ∑ k : Fin 37, ∫ t in min (BurnSchedule.time k.val:ℝ) T..
        min (BurnSchedule.time (k.val+1):ℝ) T, f k t := by
  calc
    _ = ∑ i : Fin 68,
        ((∫ t in (0:ℝ)..min (nodes i.succ:ℝ) T, f (arcs i) t)-
        (∫ t in (0:ℝ)..min (nodes i.castSucc:ℝ) T, f (arcs i) t)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact IntegralPrefix.integral_primitive_difference _ (hf _) _ _
    _ = ∑ k : Fin 37,
        ((∫ t in (0:ℝ)..min (BurnSchedule.time (k.val+1):ℝ) T, f k t)-
        (∫ t in (0:ℝ)..min (BurnSchedule.time k.val:ℝ) T, f k t)) :=
      primitive_sum (fun k t => ∫ s in (0:ℝ)..t, f k s) T
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact (IntegralPrefix.integral_primitive_difference _ (hf _) _ _).symm

theorem accumulated_arcs (x : Trajectory) (n : Fin 68) {T : ℝ}
    (ht : T ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (i : Fin 6) (k : Fin 4) :
    accumulated x n.val T i k = initial i k+
      ∑ a : Fin 37, ∫ t in min (BurnSchedule.time a.val:ℝ) T..
        min (BurnSchedule.time (a.val+1):ℝ) T, (forcing a i k).value (x.state t) := by
  have ht' : node n.val ≤ T ∧ T ≤ node (n.val+1) := by
    rw [node_start n.val n.isLt,node_finish n.val n.isLt]
    simpa only [normPiece,slot_small n.val n.isLt] using ht
  have hc := IntegralPrefix.clipped_sum (integrand x i k) node n.isLt node_monotone ht'
  have hs : (∑ j ∈ Finset.range 68,
      ∫ t in min (node j) T..min (node (j+1)) T, integrand x i k j t) =
      ∑ a : Fin 37, ∫ t in min (BurnSchedule.time a.val:ℝ) T..
        min (BurnSchedule.time (a.val+1):ℝ) T, (forcing a i k).value (x.state t) := by
    rw [Finset.sum_range]
    calc
      _ = ∑ j : Fin 68, ∫ t in min (nodes j.castSucc:ℝ) T..min (nodes j.succ:ℝ) T,
          (forcing (arcs j) i k).value (x.state t) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only
        have h₀ : node j.val = (nodes j.castSucc:ℝ) := node_eq j.castSucc
        have h₁ : node (j.val+1) = (nodes j.succ:ℝ) := node_eq j.succ
        rw [h₀,h₁]
        simp only [integrand,data,slot_small j.val j.isLt,RetainedOverlayData.arc_matches]
      _ = _ := refinement (fun a t => (forcing a i k).value (x.state t))
        (fun a => (forcing a i k).value_continuous x.continuous) T
  rw [hs] at hc
  unfold accumulated PolynomialAccumulation.boundary
  rw [hc]
  abel

end GNC.Applications.OrbitalFuel.RetainedOverlay
