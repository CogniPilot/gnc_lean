import GNC.Applications.MotorBurn.RTNAlongTrackAdjointCharges

/-! A complete scalar arrival certificate for the synthetic RTN motor burn.
It includes arbitrary continuous three-dimensional input histories, nonlinear
gravity, variable mass, computed-adjoint defects and all numerical handoffs.
The output is terminal along-track position, not a Euclidean position norm.
The common fixed pointing bias is zero; the time-varying input is not zero.
-/
noncomputable section
namespace GNC.MotorBurn.RTNAlongTrackAdjoint
open ParametricBox Set Matrix
open RTNCircle2Time6 (steps command on input)

def BoxInput (w : ℕ → ℝ → Vec3) : Prop :=
  ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ), ∀ i,
    |inputLift (w j t) i| ≤ (input j i : ℝ)

def CylinderInput (w : ℕ → ℝ → Vec3) : Prop :=
  ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
    if j < 4 then Cylinder (w j t) else w j t = 0

theorem cylinder_input_box {w : ℕ → ℝ → Vec3} (hw : CylinderInput w) : BoxInput w := by
  intro j hj t ht i
  have hc := hw j hj t ht
  rw [(RTNCircle2Time6.schedule j hj).2.2 i]
  by_cases h : j < 4
  · simp only [if_pos h] at hc
    by_cases hi : i.val = 3 ∨ i.val = 4 ∨ i.val = 5
    · simpa [h, hi] using cylinder_box hc i
    · simpa [h, hi] using cylinder_box hc i
  · simp only [if_neg h] at hc
    simp [h, hc]

theorem zero_input_box : BoxInput (fun _ _ => 0) := by
  intro j hj t ht i
  rw [(RTNCircle2Time6.schedule j hj).2.2 i]
  split_ifs <;> norm_num [inputMagnitude, forceCommand]

theorem box_input_support {w : ℕ → ℝ → Vec3} (hw : BoxInput w)
    (j : ℕ) (hj : j < 12) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (stepDuration : ℝ)) :
    |∑ i, circle.value (ell j i) t 0*inputLift (w j t) i| ≤ (boxInput j : ℝ) := by
  have hb := polynomial_pair_bound circle (ell j) (θ := 0)
    (show |t| ≤ ((1/20 : ℚ) : ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2)
    (a := 0) (by norm_num) (inputLift (w j t)) (hw j hj t ht)
  exact hb.trans (by exact_mod_cast (supports_checked j hj).2.2.2)

theorem cylinder_input_support {w : ℕ → ℝ → Vec3} (hw : CylinderInput w)
    (j : ℕ) (hj : j < 12) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (stepDuration : ℝ)) :
    |∑ i, circle.value (ell j i) t 0*inputLift (w j t) i| ≤ (cylinderInput j : ℝ) := by
  have hc := hw j hj t ht
  have hs := supports_checked j hj
  rw [(RTNCircle2Time6.schedule j hj).1] at hs
  by_cases h : j < 4
  · simp only [if_pos h, one_ne_zero, if_false] at hc hs
    have hp := cylinder_pair_bound circle (ell j) (θ := 0)
      (show |t| ≤ ((1/20 : ℚ) : ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2)
      (a := 0) (by norm_num) hs.1 hs.2.1 (w j t) hc
    exact hp.trans (by exact_mod_cast hs.2.2.1)
  · simp only [if_neg h] at hc hs
    have hz : (0 : ℝ) ≤ (cylinderInput j : ℝ) := by exact_mod_cast hs.2.2.1
    simpa [hc] using hz

private theorem zero_angle : |(0 : ℝ)| ≤ Real.pi/180 := by
  simp only [abs_zero]
  positivity

/-- All initial, interface and terminal defects are included. The independent
full-state tube is obtained from the already checked box certificate.
-/
theorem normalized_endpoint_bound {w : ℕ → ℝ → Vec3} (hw : BoxInput w)
    (x : Motion .rtn command on w 0) (supply : ℕ → ℚ)
    (hs : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
      |∑ i, circle.value (ell j i) t 0*inputLift (w j t) i| ≤ (supply j : ℝ)) :
    |x.state 11 stepDuration 1-circle.value ((steps 11).coefficients 1) stepDuration 0| ≤
      (totalCharge supply : ℝ) := by
  have he := RTNCircle2Time6.every_motion_enclosed zero_angle hw x
  have htj (j : ℕ) (hj : j < 12) : (steps j).duration = stepDuration :=
    (RTNCircle2Time6.numbers j hj).1
  have haj (j : ℕ) (hj : j < 12) : |(0 : ℝ)| ≤ ((steps j).angle : ℝ) := by
    rw [(RTNCircle2Time6.numbers j hj).2.1]
    norm_num [angle]
  have hr (j : ℕ) (hj : j < 12) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (stepDuration : ℝ)) :=
    region_of_enclosure circle (steps j) (field .rtn (command j) (on j))
      (RTNCircle2Time6.valid j hj) (haj j hj) (by simpa only [htj j hj] using ht)
      (x.state j t) (fun i => (he j hj t ht i).le)
  have hq (j : ℕ) (hj : j < 12) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (stepDuration : ℝ)) :
      ∀ i, |circle.value ((steps j).coefficients i) t 0| ≤ ((steps j).region i : ℝ) := by
    apply region_of_enclosure circle (steps j) (field .rtn (command j) (on j))
      (RTNCircle2Time6.valid j hj) (haj j hj) (by simpa only [htj j hj] using ht)
      (curve circle (steps j).coefficients 0 t)
    intro i
    simp only [sub_self, abs_zero]
    exact_mod_cast (RTNCircle2Time6.valid j hj).2.2 i |>.2.2.1.le
  let start := fun j => pairing circle (steps j).coefficients (ell j) 0 0 (x.state j 0)
  let finish := fun j => pairing circle (steps j).coefficients (ell j) 0 stepDuration
    (x.state j stepDuration)
  have hi : |start 0| ≤ (initialCharge : ℝ) := by
    have hb := initial_pair_bound circle (steps 0).coefficients (ell 0)
      (a := 0) (θ := 0) (by norm_num) (x.state 0 0) (by
        rw [x.initial]
        exact RTNCircle2Time6.initial_bound (by norm_num [angle]))
    exact hb.trans (by exact_mod_cast initial_charge_checked)
  have ha (j : ℕ) (hj : j < 12) : |finish j-start j| ≤
      (stepDuration : ℝ)*((supply j : ℝ)+charge j) := by
    have hv := RTNCircle2Time6.valid j hj
    have hb := computed_endpoint_abs_bound circle (field .rtn (command j) (on j))
      (steps j).coefficients (ell j) (h := 1/20) (a := 0) (θ := 0)
      (by norm_num) (fun i => (hv.2.2 i).1) (fun i => (hv.2.2 i).2.2.1.le)
      (by norm_num) (x.state j) (fun t => inputLift (w j t))
      (by
        intro t ht
        convert x.derivative j hj t ht using 1
        ext i
        rw [field_value]
        exact (congrFun (rate_input .rtn (fun i => (command j i : ℝ))
          (on j) (x.state j t) (w j t)) i).symm)
      (hr j hj) (hq j hj) (fun t ht i => (he j hj t ht i).le) (hs j hj)
    apply hb.trans
    have hc : (adjointCharge circle (field .rtn (command j) (on j))
        (steps j).coefficients (ell j) (steps j).region (steps j).error (1/20) 0 : ℝ) ≤
        (charge j : ℝ) := by exact_mod_cast charges_checked j hj
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hc) (by norm_num [stepDuration])
  have hj (j : ℕ) (hj : j+1 < 12) : |start (j+1)-finish j| ≤ (joinCharge j : ℝ) := by
    have hb := join_pair_bound circle (steps j).coefficients (ell j)
      (steps (j+1)).coefficients (ell (j+1)) (h := 1/20) (a := 0) (θ := 0)
      (by norm_num) (x.state j stepDuration)
      (fun i => (he j (by omega) stepDuration (by norm_num [stepDuration]) i).le)
    dsimp [start, finish]
    rw [x.join j hj]
    exact hb.trans (by exact_mod_cast joins_charge_checked j (by omega))
  have hall := finite_pair_chain start finish
    (fun j => (stepDuration : ℝ)*((supply j : ℝ)+charge j))
    (fun j => (joinCharge j : ℝ)) (initialCharge : ℝ) 12 hi ha hj 11 (by omega)
  have hterm := terminal_pair_bound circle (steps 11).coefficients (ell 11) terminalRow
    (h := 1/20) (a := 0) (θ := 0) (by norm_num) (x.state 11 stepDuration)
    (fun i => (he 11 (by omega) stepDuration (by norm_num [stepDuration]) i).le)
  have hrow : (∑ i, (terminalRow i : ℝ)*(x.state 11 stepDuration i-
      circle.value ((steps 11).coefficients i) stepDuration 0)) =
      x.state 11 stepDuration 1-circle.value ((steps 11).coefficients 1) stepDuration 0 := by
    have hc (i : Fin 13) : (terminalRow i : ℝ) = if i = 1 then 1 else 0 := by
      by_cases h : i = 1 <;> simp [terminalRow, h]
    simp_rw [hc, ite_mul, one_mul, zero_mul]
    simp
  change |(∑ i, (terminalRow i : ℝ)*(x.state 11 stepDuration i-
      circle.value ((steps 11).coefficients i) stepDuration 0))-finish 11| ≤
      (terminalPairCharge circle (ell 11) terminalRow (steps 11).error (1/20) 0 : ℝ) at hterm
  rw [hrow] at hterm
  have htc : (terminalPairCharge circle (ell 11) terminalRow (steps 11).error (1/20) 0 : ℝ) ≤
      (terminalCharge : ℝ) := by exact_mod_cast terminal_charge_checked
  have hb := (abs_add_le (_-finish 11) (finish 11)).trans
    (add_le_add (hterm.trans htc) hall)
  rw [sub_add_cancel] at hb
  apply hb.trans_eq
  simp only [totalCharge, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat, stepDuration]
  push_cast
  ring

theorem endpoint_bound {w : ℕ → ℝ → Vec3} (hw : BoxInput w)
    (x : Motion .rtn command on w 0) (cylinder : Bool)
    (hs : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
      |∑ i, circle.value (ell j i) t 0*inputLift (w j t) i| ≤
        ((if cylinder then cylinderInput else boxInput) j : ℝ)) :
    |(ApproachGate.radiusSI : ℝ)*(x.state 11 stepDuration 1-
      circle.value ((steps 11).coefficients 1) stepDuration 0)| ≤ (positionBound cylinder : ℝ) := by
  rw [abs_mul, abs_of_nonneg (by norm_num [ApproachGate.radiusSI] : (0 : ℝ) ≤ ApproachGate.radiusSI)]
  exact (mul_le_mul_of_nonneg_left (normalized_endpoint_bound hw x _ hs)
    (by norm_num [ApproachGate.radiusSI])).trans (by exact_mod_cast totals_checked cylinder)

/-- Difference from an actual undisturbed solution, not just from a stored
polynomial. The numerical nominal error is included a second time here.
-/
theorem reference_bound {w : ℕ → ℝ → Vec3} (hw : BoxInput w)
    (x : Motion .rtn command on w 0) (reference : Motion .rtn command on (fun _ _ => 0) 0)
    (cylinder : Bool)
    (hs : ∀ j < 12, ∀ t ∈ Icc (0 : ℝ) (stepDuration : ℝ),
      |∑ i, circle.value (ell j i) t 0*inputLift (w j t) i| ≤
        ((if cylinder then cylinderInput else boxInput) j : ℝ)) :
    |(ApproachGate.radiusSI : ℝ)*(x.state 11 stepDuration 1-reference.state 11 stepDuration 1)| ≤
      (relativePositionBound cylinder : ℝ) := by
  have hx := normalized_endpoint_bound hw x _ hs
  have hr := normalized_endpoint_bound zero_input_box reference (fun _ => 0)
    (by intros; simp)
  have hb := (abs_add_le (x.state 11 stepDuration 1-
    circle.value ((steps 11).coefficients 1) stepDuration 0)
    (-(reference.state 11 stepDuration 1-circle.value ((steps 11).coefficients 1) stepDuration 0))).trans
      (add_le_add hx (by simpa only [abs_neg] using hr))
  have he : (x.state 11 stepDuration 1-circle.value ((steps 11).coefficients 1) stepDuration 0)+
      -(reference.state 11 stepDuration 1-circle.value ((steps 11).coefficients 1) stepDuration 0) =
      x.state 11 stepDuration 1-reference.state 11 stepDuration 1 := by ring
  rw [he] at hb
  rw [abs_mul, abs_of_nonneg (by norm_num [ApproachGate.radiusSI] : (0 : ℝ) ≤ ApproachGate.radiusSI)]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num [ApproachGate.radiusSI])).trans
    (by exact_mod_cast relative_totals_checked cylinder)

theorem cylinder_reference_bound {w : ℕ → ℝ → Vec3} (hw : CylinderInput w)
    (x : Motion .rtn command on w 0) (reference : Motion .rtn command on (fun _ _ => 0) 0) :
    |(ApproachGate.radiusSI : ℝ)*(x.state 11 stepDuration 1-reference.state 11 stepDuration 1)| ≤
      695.64 := by
  have h := reference_bound (cylinder_input_box hw) x reference true (cylinder_input_support hw)
  norm_num [relativePositionBound] at h ⊢
  exact h

theorem box_reference_bound {w : ℕ → ℝ → Vec3} (hw : BoxInput w)
    (x : Motion .rtn command on w 0) (reference : Motion .rtn command on (fun _ _ => 0) 0) :
    |(ApproachGate.radiusSI : ℝ)*(x.state 11 stepDuration 1-reference.state 11 stepDuration 1)| ≤
      1655.61 := by
  have h := reference_bound hw x reference false (box_input_support hw)
  norm_num [relativePositionBound] at h ⊢
  exact h

theorem exists_physical_reference (w : ℕ → ℝ → Vec3)
    (hwc : ∀ j < 12, Continuous (w j)) (hw : CylinderInput w) :
    ∃ x : Motion .rtn command on w 0,
      ∃ reference : Motion .rtn command on (fun _ _ => 0) 0,
        x.Physical ∧ reference.Physical ∧
        |(ApproachGate.radiusSI : ℝ)*(x.state 11 stepDuration 1-reference.state 11 stepDuration 1)| ≤
          695.64 := by
  obtain ⟨x, hxp, _⟩ := RTNCircle2Time6.exists_physical_enclosed zero_angle w hwc
    (cylinder_input_box hw)
  obtain ⟨reference, hrp, _⟩ := RTNCircle2Time6.exists_physical_enclosed zero_angle
    (fun _ _ => 0) (by intros; exact continuous_const) zero_input_box
  exact ⟨x, reference, hxp, hrp, cylinder_reference_bound hw x reference⟩

/-- The reported component is a physical inertial displacement projected
onto the reference's terminal along-track unit direction. -/
theorem along_track_projection (z q : Fin 13 → ℝ) (phase : ℝ) :
    rotate (AxisRotation.zRotation phase) ![0,1,0] ⬝ᵥ
      ((ApproachGate.radiusSI : ℝ) •
        (CircularRendezvous3D.inertialPosition phase (project z)-
          CircularRendezvous3D.inertialPosition phase (project q))) =
      (ApproachGate.radiusSI : ℝ)*(z 1-q 1) := by
  rw [dotProduct_smul, CircularRendezvous3D.inertialPosition,
    CircularRendezvous3D.inertialPosition, ← rotate_sub, rotate_dot]
  simp [project, first, firstIndex, ApproachGate.project, CircularRendezvous3D.position,
    dotProduct, Fin.sum_univ_succ]

end GNC.MotorBurn.RTNAlongTrackAdjoint
