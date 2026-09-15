import GNC.Applications.OrbitalComparison.PointingCapSupport
import GNC.Applications.OrbitalComparison.PointingCapObstruction
import GNC.Applications.OrbitalComparison.PointingCapReachable

/-! A concrete terminal support query in the final reference RTN frame.
The unit normal `(0,3/5,4/5)` includes along-track and out-of-plane motion.
Finite polynomial certificates are connected to all physical trajectories,
with the complete prediction error charged once. -/
namespace GNC.OrbitalComparison.PointingCapClearance
open ParameterPolynomial PointingCapSupport PointingCapCertificate
open PointingCapBurn SpatialBurn Set

def projection (D : Data) : Coefficients :=
  add (scale (3/5) (D.q 1)) (scale (4/5) (D.q 2))

noncomputable section

def observable (z : E3) : ℝ := (3/5)*z 1+(4/5)*z 2

theorem observable_norm (z : E3) : |observable z| ≤ ‖z‖ := by
  have hn : ‖pack 0 (3/5) (4/5)‖=1 := by
    have h := pack_norm_sq 0 (3/5) (4/5)
    nlinarith [norm_nonneg (pack 0 (3/5) (4/5))]
  have hi : inner ℝ (pack 0 (3/5) (4/5)) z=observable z := by
    change dotProduct z.ofLp (star (pack 0 (3/5) (4/5)).ofLp)=observable z
    simp [pack_eq,dotProduct,Fin.sum_univ_succ,observable]
    ring
  simpa only [hi,hn,one_mul] using
    abs_real_inner_le_norm (pack 0 (3/5) (4/5)) z

theorem observable_sub (z w : E3) :
    observable (z-w)=observable z-observable w := by
  simp only [observable,PiLp.sub_apply]
  ring

theorem projection_value (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    value (projection D) x t=observable (D.displacement x t) := by
  simp [projection,value_add,value_scale,observable,Data.displacement,
    PointingCapPolynomial.vectorValue,pack_eq]

theorem candidate_frame (D : Data) (ha : D.alpha=2) (x : Fin 3 → ℝ) :
    PointingCapObstruction.framed (D.position x 1)=D.displacement x 1 := by
  simp only [PointingCapObstruction.framed,Data.position,PointingCapFrame.position,
    PointingCapFrame.turn,ha,Rat.cast_ofNat,mul_one,add_sub_cancel_left,
    PointingCapObstruction.turn_inverse]

theorem physical_error (D : Data) (h : D.Valid) (ha : D.alpha=2)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x)
    (X : Motion (D.alpha:ℝ) (direction x)) :
    |observable (PointingCapObstruction.framed (X.p 1))-
      value (projection D) x 1|≤(D.positionError:ℝ) := by
  rw [projection_value,←candidate_frame D ha,←observable_sub]
  apply (observable_norm _).trans
  rw [PointingCapObstruction.frame_difference]
  exact (D.certifies h hx X 1 (by norm_num)).1

theorem physical_upper (D : Data) (h : D.Valid) (ha : D.alpha=2)
    (C : Certificate) (hc : C.Valid (projection D) D.sigma) (ht : C.time=1)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x)
    (X : Motion (D.alpha:ℝ) (direction x)) :
    observable (PointingCapObstruction.framed (X.p 1))≤
      (C.upper:ℝ)+(D.positionError:ℝ) := by
  have hb := C.bounds (projection D) D.sigma hc hx
  rw [ht,Rat.cast_one] at hb
  have he := (abs_le.mp (physical_error D h ha hx X)).2
  linarith

theorem physical_witness (D : Data) (h : D.Valid) (ha : D.alpha=2)
    (x : Fin 3 → ℚ) (hx : Admissible (D.sigma:ℝ) (fun i => (x i:ℝ))) :
    ∃ z ∈ D.reachablePositions 1,
      (rationalValue (projection D) x 1:ℝ)-(D.positionError:ℝ)≤
        observable (PointingCapObstruction.framed z) := by
  let X := D.trajectory h (fun i => (x i:ℝ)) hx
  refine ⟨X.p 1,?_,?_⟩
  · exact ⟨fun i => (x i:ℝ),hx,X,rfl⟩
  · have he := (abs_le.mp (physical_error D h ha hx X)).1
    rw [rationalValue_cast,Rat.cast_one]
    linarith

/-- Largest attainable terminal displacement in the chosen unit direction.
The support bounds below establish nonemptiness and boundedness as well. -/
def support (D : Data) : ℝ :=
  sSup ((fun z => observable (PointingCapObstruction.framed z)) ''
    D.reachablePositions 1)

theorem support_eq {D₁ D₂ : Data}
    (ha : D₁.alpha=D₂.alpha) (hs : D₁.sigma=D₂.sigma) :
    support D₁=support D₂ := by
  unfold support
  rw [Data.reachablePositions_eq ha hs]

theorem physical_support_bounds (D : Data) (h : D.Valid) (ha : D.alpha=2)
    (C : Certificate) (hc : C.Valid (projection D) D.sigma) (ht : C.time=1)
    (x : Fin 3 → ℚ) (hx : Admissible (D.sigma:ℝ) (fun i => (x i:ℝ))) :
    (rationalValue (projection D) x 1:ℝ)-(D.positionError:ℝ)≤support D ∧
      support D≤(C.upper:ℝ)+(D.positionError:ℝ) := by
  obtain ⟨z,hz,hl⟩ := physical_witness D h ha x hx
  let S := (fun z => observable (PointingCapObstruction.framed z)) '' D.reachablePositions 1
  have hb : ∀ y ∈ S, y≤(C.upper:ℝ)+(D.positionError:ℝ) := by
    rintro y ⟨w,⟨x,hx,X,rfl⟩,rfl⟩
    exact physical_upper D h ha C hc ht hx X
  have hs : observable (PointingCapObstruction.framed z)∈S := ⟨z,hz,rfl⟩
  exact ⟨hl.trans (le_csSup ⟨_,hb⟩ hs),csSup_le ⟨_,hs⟩ hb⟩

theorem halfspace_clearance (D : Data) (h : D.Valid) (ha : D.alpha=2)
    (C : Certificate) (hc : C.Valid (projection D) D.sigma) (ht : C.time=1)
    (limit : ℝ) (hl : (C.upper:ℝ)+(D.positionError:ℝ)<limit) :
    Disjoint (D.reachablePositions 1)
      {z | limit≤observable (PointingCapObstruction.framed z)} := by
  rw [Set.disjoint_left]
  rintro z ⟨x,hx,X,rfl⟩ hz
  exact (physical_upper D h ha C hc ht hx X).not_gt (hl.trans_le hz)

end
end GNC.OrbitalComparison.PointingCapClearance
