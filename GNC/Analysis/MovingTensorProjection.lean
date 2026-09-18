import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic
import GNC.Analysis.DefectBound

/-! Exact error from replacing a moving tensor projection by its retained
subspace dynamics. The second-order TDSTT closure of Zhou et al.
(arXiv:2412.07060v1, equations 47--56) discards these mixed terms.
Equation 47 explicitly introduces an approximation. This error is distinct
from Taylor truncation and numerical integration error. No eigensolver
correctness or smallness of the omitted term is assumed here. -/
noncomputable section
namespace GNC.MovingTensorProjection
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev Tensor := E →L[ℝ] E →L[ℝ] F

def normal (P : E →L[ℝ] E) (v' : E) : E := v'-P v'

def defect (T : Tensor (E := E) (F := F)) (P : E →L[ℝ] E)
    (v w v' w' : E) : F := T (normal P v') w+T v (normal P w')

def retainedDerivative (T T' : Tensor (E := E) (F := F))
    (P : E →L[ℝ] E) (v w v' w' : E) : F :=
  T' v w+T (P v') w+T v (P w')

def projected (T : Tensor (E := E) (F := F)) (P : E →L[ℝ] E) :
    Tensor (E := E) (F := F) := T.bilinearComp P P

theorem projected_mixed_zero (T : Tensor (E := E) (F := F))
    (P : E →L[ℝ] E) (hP : ∀ x, P (P x)=P x) (v w : E) :
    projected T P (normal P v) w=0 ∧ projected T P w (normal P v)=0 := by
  simp [projected,ContinuousLinearMap.bilinearComp_apply,normal,map_sub,hP]

/-- Idempotence and orthogonality are not needed for this exact split. -/
theorem derivative_split
    (T : ℝ → Tensor (E := E) (F := F)) (v w : ℝ → E)
    (T' : Tensor (E := E) (F := F)) (v' w' : E) (t : ℝ)
    (P : E →L[ℝ] E) (hT : HasDerivAt T T' t)
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => T s (v s) (w s))
      (retainedDerivative (T t) T' P (v t) (w t) v' w'+
        defect (T t) P (v t) (w t) v' w') t := by
  convert (hT.clm_apply hv).clm_apply hw using 1
  simp only [retainedDerivative,defect,normal,map_sub,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply]
  abel

/-- Only the discarded tensor contributes if the retained tensor has no
mixed normal/tangent components. -/
theorem defect_discarded (T S : Tensor (E := E) (F := F))
    (P : E →L[ℝ] E) (v w v' w' : E)
    (hleft : S (normal P v') w=0) (hright : S v (normal P w')=0) :
    defect T P v w v' w'=defect (T-S) P v w v' w' := by
  simp [defect,ContinuousLinearMap.sub_apply,hleft,hright]

theorem bilinear_bound (T : Tensor (E := E) (F := F)) (v w : E) :
    ‖T v w‖≤‖T‖*‖v‖*‖w‖ := by
  exact (T v).le_opNorm w |>.trans
    (mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg w))

theorem defect_bound (T : Tensor (E := E) (F := F))
    (P : E →L[ℝ] E) (v w v' w' : E) :
    ‖defect T P v w v' w'‖≤
      ‖T‖*(‖normal P v'‖*‖w‖+‖v‖*‖normal P w'‖) := by
  calc
    _≤‖T (normal P v') w‖+‖T v (normal P w')‖ := norm_add_le _ _
    _≤‖T‖*‖normal P v'‖*‖w‖+‖T‖*‖v‖*‖normal P w'‖ :=
      add_le_add (bilinear_bound _ _ _) (bilinear_bound _ _ _)
    _=_ := by ring

theorem discarded_defect_bound (T S : Tensor (E := E) (F := F))
    (P : E →L[ℝ] E) (v w v' w' : E)
    (hleft : S (normal P v') w=0) (hright : S v (normal P w')=0) :
    ‖defect T P v w v' w'‖≤
      ‖T-S‖*(‖normal P v'‖*‖w‖+‖v‖*‖normal P w'‖) := by
  rw [defect_discarded T S P v w v' w' hleft hright]
  exact defect_bound _ _ _ _ _ _

/-- For an actual projected tensor, idempotence discharges both mixed
component hypotheses. An orthogonal subspace projector is a special case. -/
theorem projection_defect_bound (T : Tensor (E := E) (F := F))
    (P : E →L[ℝ] E) (hP : ∀ x, P (P x)=P x) (v w v' w' : E) :
    ‖defect T P v w v' w'‖≤
      ‖T-projected T P‖*(‖normal P v'‖*‖w‖+‖v‖*‖normal P w'‖) := by
  exact discarded_defect_bound T (projected T P) P v w v' w'
    (projected_mixed_zero T P hP v' w).1 (projected_mixed_zero T P hP w' v).2

theorem unit_diagonal_bound (T S : Tensor (E := E) (F := F))
    (P : E →L[ℝ] E) (v v' : E) (hv : ‖v‖=1)
    (hleft : S (normal P v') v=0) (hright : S v (normal P v')=0) :
    ‖defect T P v v v' v'‖≤2*‖T-S‖*‖normal P v'‖ := by
  have h := discarded_defect_bound T S P v v v' v' hleft hright
  rw [hv] at h
  convert h using 1 <;> ring

/-- The 1/2 Taylor weight cancels the two slot contributions. -/
theorem quadratic_weight_bound (T S : Tensor (E := E) (F := F))
    (P : E →L[ℝ] E) (v v' : E) (hv : ‖v‖=1)
    (hleft : S (normal P v') v=0) (hright : S v (normal P v')=0)
    (a : ℝ) :
    ‖(a^2/2) • defect T P v v v' v'‖≤
      a^2*‖T-S‖*‖normal P v'‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤a^2/2)]
  calc
    _≤(a^2/2)*(2*‖T-S‖*‖normal P v'‖) :=
      mul_le_mul_of_nonneg_left (unit_diagonal_bound T S P v v' hv hleft hright) (by positivity)
    _=_ := by ring

theorem defect_zero_of_closed (T : Tensor (E := E) (F := F))
    (P : E →L[ℝ] E) (v w v' w' : E) (hv : P v'=v') (hw : P w'=w') :
    defect T P v w v' w'=0 := by
  simp [defect,normal,hv,hw]

/-- A full moving basis has no projection loss. -/
theorem full_basis_exact (T : Tensor (E := E) (F := F)) (v w v' w' : E) :
    defect T (ContinuousLinearMap.id ℝ E) v w v' w'=0 := by
  exact defect_zero_of_closed T _ v w v' w' rfl rfl

/-- Integrating a checked transport-defect bound yields a coefficient error
bound. A separate Taylor remainder and numerical residual are still needed
to turn a reduced tensor into a physical-flow prediction certificate. -/
theorem propagated_defect_bound [CompleteSpace F]
    (Φ : ℝ → (F →L[ℝ] F)ˣ) (A : ℝ → F →L[ℝ] F)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (actual reduced forcing : ℝ → F)
    (T S : ℝ → Tensor (E := E) (F := F)) (P : ℝ → E →L[ℝ] E)
    (v v' : ℝ → E) {a b R speed gain : ℝ}
    (hab : a≤b) (hR : 0≤R) (hspeed : 0≤speed)
    (hd : Continuous (fun t => defect (T t) (P t) (v t) (v t) (v' t) (v' t)))
    (hactual : ∀ t ∈ Set.Icc a b, HasDerivAt actual
      (A t (actual t)+forcing t+defect (T t) (P t) (v t) (v t) (v' t) (v' t)) t)
    (hreduced : ∀ t ∈ Set.Icc a b,
      HasDerivAt reduced (A t (reduced t)+forcing t) t)
    (hunit : ∀ t ∈ Set.Icc a b, ‖v t‖=1)
    (hleft : ∀ t ∈ Set.Icc a b, S t (normal (P t) (v' t)) (v t)=0)
    (hright : ∀ t ∈ Set.Icc a b, S t (v t) (normal (P t) (v' t))=0)
    (hdiscard : ∀ t ∈ Set.Icc a b, ‖T t-S t‖≤R)
    (hvelocity : ∀ t ∈ Set.Icc a b, ‖normal (P t) (v' t)‖≤speed)
    (hgain : (∫ t in a..b, ‖DefectBound.kernel Φ b t‖)≤gain)
    (hinit : actual a=reduced a) :
    ‖actual b-reduced b‖≤gain*(2*R*speed) := by
  have hbound (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖defect (T t) (P t) (v t) (v t) (v' t) (v' t)‖≤2*R*speed := by
    apply (unit_diagonal_bound (T t) (S t) (P t) (v t) (v' t)
      (hunit t ht) (hleft t ht) (hright t ht)).trans
    gcongr
    · exact hdiscard t ht
    · exact hvelocity t ht
  have h := DefectBound.error_bound Φ A hΦ reduced actual forcing
    (fun t => defect (T t) (P t) (v t) (v t) (v' t) (v' t))
    hab hd hreduced hactual (by positivity) hbound hgain
  simpa [hinit] using h

/-- A constant off-diagonal tensor restricted to (cos t,sin t) has a
changing projection, even though its own time derivative is zero. -/
theorem rotating_mixed_entry_derivative :
    HasDerivAt (fun t : ℝ => 2*Real.sin t*Real.cos t) 2 0 := by
  convert ((Real.hasDerivAt_sin 0).const_mul 2).mul (Real.hasDerivAt_cos 0) using 1 <;> norm_num

section Reconstruction
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Synthesizing a reduced tensor with moving directions introduces its own
kinematic defect. This is distinct from the discarded full-tensor defect:
it uses only the retained tensor and the directions' normal motion. -/
def synthesisDefect (S : Tensor (E := U) (F := F)) (R N : E →L[ℝ] U)
    (x : E) : F := (1/2:ℝ) • (S (N x) (R x)+S (R x) (N x))

theorem synthesized_derivative
    (S : ℝ → Tensor (E := U) (F := F)) (R : ℝ → E →L[ℝ] U)
    (S' V : Tensor (E := U) (F := F)) (B : U →L[ℝ] U)
    (N : E →L[ℝ] U) (x : E) (t : ℝ)
    (hS : HasDerivAt S S' t)
    (hR : HasDerivAt R (B.comp (R t)+N) t)
    (htransport : ∀ v w, S' v w=V v w-S t (B v) w-S t v (B w)) :
    HasDerivAt (fun s => (1/2:ℝ) • S s (R s x) (R s x))
      ((1/2:ℝ) • V (R t x) (R t x)+synthesisDefect (S t) (R t) N x) t := by
  have hr := hR.clm_apply (hasDerivAt_const t x)
  have hs := ((hS.clm_apply hr).clm_apply hr).const_smul (1/2:ℝ)
  convert hs using 1
  simp only [synthesisDefect,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,map_zero,add_zero,htransport,
    map_add,ContinuousLinearMap.add_apply]
  module

theorem synthesis_defect_bound
    (S : Tensor (E := U) (F := F)) (R N : E →L[ℝ] U) (x : E) :
    ‖synthesisDefect S R N x‖≤‖S‖*‖N‖*‖R‖*‖x‖^2 := by
  have h1 := bilinear_bound S (N x) (R x)
  have h2 := bilinear_bound S (R x) (N x)
  have hn := N.le_opNorm x
  have hr := R.le_opNorm x
  have hsum := (norm_add_le (S (N x) (R x)) (S (R x) (N x))).trans
    (add_le_add h1 h2)
  have hbound : ‖S (N x) (R x)+S (R x) (N x)‖≤
      2*(‖S‖*‖N‖*‖R‖*‖x‖^2) := by
    apply hsum.trans
    calc
      _≤‖S‖*(‖N‖*‖x‖)*(‖R‖*‖x‖)+‖S‖*(‖R‖*‖x‖)*(‖N‖*‖x‖) := by gcongr
      _=_ := by ring
  rw [synthesisDefect,norm_smul,Real.norm_eq_abs]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  linarith

theorem synthesis_defect_zero (S : Tensor (E := U) (F := F))
    (R : E →L[ℝ] U) (x : E) : synthesisDefect S R 0 x=0 := by
  simp [synthesisDefect]

end Reconstruction

end GNC.MovingTensorProjection
