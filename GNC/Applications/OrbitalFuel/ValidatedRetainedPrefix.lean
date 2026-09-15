import GNC.Applications.OrbitalFuel.RetainedPrefixTheory
import GNC.Applications.OrbitalFuel.RetainedPrefixData

/-! Uniform accumulated-forcing error throughout all 68 overlay intervals.
The forcing is evaluated on the actual validated reference/transition flow.
No numerical quadrature or sampled error maximum enters the theorem.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.ValidatedRetainedPrefix
open GNC GNC.PolynomialAccumulation RetainedPrefix PolynomialBurn

def slot (n : ℕ) : Fin 68 := ⟨min n 67,by omega⟩

theorem slot_small (n : ℕ) (hn : n < 68) : slot n = ⟨n,hn⟩ := by
  apply Fin.ext
  simp only [slot, Fin.val_mk]
  omega

def normPiece (n : ℕ) : RetainedNorm.Piece := RetainedNormData.pieces (slot n)
def data (n : ℕ) : Data := RetainedPrefixData.pieces (slot n)
def node (n : ℕ) : ℝ := if n < 68 then (normPiece n).start else 3/5
def origin (n : ℕ) : ℝ := (normPiece n).offset
def coefficients (i : Fin 6) (k : Fin 4) (n : ℕ) : List ℚ := (data n).pulled i k
def integrand (x : Trajectory) (i : Fin 6) (k : Fin 4) (n : ℕ) (t : ℝ) : ℝ :=
  (forcing (data n).arc i k).value (x.state t)
def initial (i : Fin 6) (k : Fin 4) : ℝ := if k = 0 then (RetainedPrefixData.initial i:ℝ) else 0
def accumulated (x : Trajectory) (n : ℕ) (t : ℝ) (i : Fin 6) (k : Fin 4) : ℝ :=
  boundary (initial i k) (integrand x i k) node n+∫ s in node n..t, integrand x i k n s

theorem node_zero : node 0 = 0 := by
  simpa [node, normPiece, slot] using congrArg (fun q : ℚ => (q:ℝ)) RetainedNormData.initial

theorem origin_zero : origin 0 = 0 := by
  have h : (normPiece 0).offset = 0 := by decide +kernel
  unfold origin
  exact_mod_cast h

theorem node_start (n : ℕ) (hn : n < 68) : node n = ((normPiece n).start:ℝ) := by
  simp only [node, if_pos hn]

theorem node_finish (n : ℕ) (hn : n < 68) : node (n+1) = ((normPiece n).finish:ℝ) := by
  by_cases hs : n+1 < 68
  · have hj := RetainedNormData.joins ⟨n,by omega⟩
    have hcast := congrArg (fun q : ℚ => (q:ℝ)) hj
    simpa only [node, if_pos hs, normPiece, slot_small n hn, slot_small (n+1) hs] using hcast.symm
  · have he : n = 67 := by omega
    subst n
    rw [node, if_neg (by omega)]
    simp [normPiece, slot, RetainedNormData.final]

theorem node_order (n : ℕ) (hn : n < 68) : node n ≤ node (n+1) := by
  rw [node_start n hn, node_finish n hn]
  exact_mod_cast (RetainedNormData.valid (slot n)).1

theorem integrand_continuous (x : Trajectory) (i : Fin 6) (k : Fin 4) (n : ℕ) :
    Continuous (integrand x i k n) :=
  (forcing (data n).arc i k).value_continuous x.continuous

theorem rate_error (x : Trajectory) (i : Fin 6) (k : Fin 4) (n : ℕ) (hn : n < 68)
    {t : ℝ} (ht : t ∈ Set.Icc (node n) (node (n+1))) :
    |integrand x i k n t-rate (coefficients i k n) (origin n) t| ≤ 1/10^14+1/10^18 := by
  rw [node_start n hn, node_finish n hn] at ht
  exact (data n).rate_error (normPiece n) (RetainedPrefixData.valid (slot n))
    (RetainedNormData.valid (slot n)) x i k ht

theorem jump_error (i : Fin 6) (k : Fin 4) (n : ℕ) (hn : n+1 < 68) :
    |value (coefficients i k n) (origin n) (node (n+1))-
      value (coefficients i k (n+1)) (origin (n+1)) (node (n+1))| ≤ 1/10^18 := by
  have hn' : n < 68 := by omega
  have hc := RetainedPrefixData.joins ⟨n,by omega⟩
  have h := Data.jump_error _ _ _ _ hc i k
  have hj := congrArg (fun q : ℚ => (q:ℝ)) hc.1
  dsimp only at hj
  rw [hj] at h
  simpa only [coefficients, data, origin, normPiece, node, if_pos hn,
    slot_small n hn', slot_small (n+1) hn] using h

theorem initial_error (i : Fin 6) (k : Fin 4) :
    |initial i k-value (coefficients i k 0) (origin 0) (node 0)| ≤ 1/10^18 := by
  rw [node_zero,origin_zero]
  have h := (Rat.cast_le (K := ℝ)).mpr (RetainedPrefixData.initial_error i k)
  have he := GNC.Planning.PolynomialKernel.evaluate_map (Rat.castHom ℝ)
    ((RetainedPrefixData.pieces 0).pulled i k) 0
  simp only [map_zero] at he
  change GNC.Planning.PolynomialKernel.evaluate
    (((RetainedPrefixData.pieces 0).pulled i k).map (Rat.castHom ℝ)) 0 =
      ((GNC.Planning.PolynomialKernel.evaluate ((RetainedPrefixData.pieces 0).pulled i k) 0:ℚ):ℝ) at he
  simp only [value, sub_self, coefficients, data, show slot 0 = 0 from rfl, he]
  by_cases hk : k = 0 <;> simp only [initial, if_pos, hk] at * <;>
    norm_num at h ⊢ <;> exact h

/-- A uniform bound for each accumulated coefficient column, including the
partial last interval. The remaining forward transition is applied once. -/
theorem enclosure (x : Trajectory) (n : Fin 68) {t : ℝ}
    (ht : t ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (i : Fin 6) (k : Fin 4) :
    |accumulated x n.val t i k-
      value ((RetainedPrefixData.pieces n).pulled i k)
        ((RetainedNormData.pieces n).offset:ℝ) t| ≤ 1/10^14 := by
  have ht' : t ∈ Set.Icc (node n.val) (node (n.val+1)) := by
    rw [node_start n.val n.isLt, node_finish n.val n.isLt]
    simpa only [normPiece, slot_small n.val n.isLt] using ht
  have h := prefix_error (initial i k) (integrand x i k) node origin (coefficients i k) n.val
    (initial_error i k) (fun j hj => node_order j (by omega))
    (fun j _ => (integrand_continuous x i k j).intervalIntegrable _ _)
    (fun j hj s hs => rate_error x i k j (by omega) hs)
    (fun j hj => jump_error i k j (by omega)) ht'.1
    ((integrand_continuous x i k n.val).intervalIntegrable _ _)
    (fun s hs => rate_error x i k n.val n.isLt ⟨hs.1,hs.2.trans ht'.2⟩)
  have hh : (node (n.val+1)) ≤ 3/5 := by
    rw [node_finish n.val n.isLt]
    have hp := RetainedNormData.valid n
    have hr : (RetainedNormData.pieces n).offset+3/160 ≤ 3/5 := by
      have hn := (RetainedNormData.pieces n).referenceStep.isLt
      dsimp only [RetainedNorm.Piece.offset]
      have hnQ : ((RetainedNormData.pieces n).referenceStep.val:ℚ) ≤ 31 := by exact_mod_cast (show _ ≤ 31 by omega)
      linarith
    have hb := (Rat.cast_le (K := ℝ)).mpr (hp.2.2.1.trans hr)
    norm_num at hb ⊢
    simpa only [normPiece, slot_small n.val n.isLt] using hb
  have hnR : (n.val:ℝ) ≤ 67 := by exact_mod_cast (show n.val ≤ 67 by omega)
  rw [node_zero] at h
  change |accumulated x n.val t i k-value (coefficients i k n.val) (origin n.val) t| ≤ _ at h
  have hb : |accumulated x n.val t i k-value (coefficients i k n.val) (origin n.val) t| ≤ 1/10^14 := by
    norm_num at h ⊢
    linarith [ht'.2.trans hh]
  simpa only [coefficients, data, origin, normPiece, slot_small n.val n.isLt] using hb

theorem all_time_enclosure (x : Trajectory) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (3/5)) :
    ∃ n : Fin 68, t ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ) ∧ ∀ i : Fin 6, ∀ k : Fin 4,
        |accumulated x n.val t i k-
          value ((RetainedPrefixData.pieces n).pulled i k)
            ((RetainedNormData.pieces n).offset:ℝ) t| ≤ 1/10^14 := by
  obtain ⟨n,hn⟩ := RetainedNormData.coverage ht
  exact ⟨n,hn,fun i k => enclosure x n hn i k⟩

end GNC.Applications.OrbitalFuel.ValidatedRetainedPrefix
