import GNC.Applications.OrbitalFuel.RetainedPrefixData
import GNC.Applications.OrbitalFuel.BurnSchedule

/-! Exact refinement of the 37 burn/coast arcs by the 68 polynomial intervals.
The primitive cancellation is valid for arbitrary functions and query times.
-/
namespace GNC.Applications.OrbitalFuel.RetainedOverlayData
open Matrix
set_option autoImplicit false

def nodes : Fin 69 → ℚ := ![0, (1/150), (3/160), (2/75), (3/80), (1/25), (9/160), (3/50), (11/150), (3/40), (7/75), (3/32), (8/75), (9/80), (19/150), (21/160), (7/50), (3/20), (4/25), (27/160), (13/75), (3/16), (29/150), (33/160), (31/150), (9/40), (17/75), (6/25), (39/160), (13/50), (21/80), (41/150), (9/32), (22/75), (3/10), (23/75), (51/160), (49/150), (27/80), (17/50), (57/160), (9/25), (28/75), (3/8), (59/150), (63/160), (61/150), (33/80), (32/75), (69/160), (11/25), (9/20), (23/50), (15/32), (71/150), (39/80), (37/75), (81/160), (38/75), (21/40), (79/150), (27/50), (87/160), (14/25), (9/16), (43/75), (93/160), (89/150), (3/5)]

def arcs : Fin 68 → Fin 37 := ![0, 1, 1, 2, 2, 3, 3, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 23, 23, 24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29, 30, 30, 31, 31, 32, 33, 33, 34, 34, 35, 35, 36]

set_option maxRecDepth 100000 in
theorem node_matches : ∀ n : Fin 69,
    (if h : n.val < 68 then (RetainedNormData.pieces ⟨n.val,h⟩).start else 3/5) = nodes n := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem finish_matches : ∀ n : Fin 68, (RetainedNormData.pieces n).finish = nodes n.succ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem arc_matches : ∀ n : Fin 68, (RetainedPrefixData.pieces n).arc = arcs n := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem primitive_sum {E : Type*} [AddCommGroup E] (A : Fin 37 → ℝ → E) (T : ℝ) :
    (∑ i : Fin 68, (A (arcs i) (min (nodes i.succ:ℝ) T)-
      A (arcs i) (min (nodes i.castSucc:ℝ) T))) =
      ∑ k : Fin 37, (A k (min (BurnSchedule.time (k.val+1):ℝ) T)-
        A k (min (BurnSchedule.time k.val:ℝ) T)) := by
  norm_num [nodes,arcs,BurnSchedule.time,Fin.sum_univ_succ,Fin.succ]
  abel!

end GNC.Applications.OrbitalFuel.RetainedOverlayData
