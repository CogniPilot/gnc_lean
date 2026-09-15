import GNC.Applications.Rendezvous.EndpointCertificate

/-! A concrete two-burn certificate carries all numeric proof obligations.
Applying `Plan.terminal` requires only the displayed physical trajectory and
its initial condition, not assumed propagation-error allowances.
-/
noncomputable section
namespace GNC.Applications.Rendezvous.EndpointMission
open GNC.PolynomialODE GNC.Planning.PolynomialKernel EndpointCertificate

def initialQ : Fin 5 → ℚ := ![-2/196000001,-28000/196000001,0,0,1]
def initial : Fin 4 → ℝ := ![-2/196000001,-28000/196000001,0,0]

theorem initial_lift (i : Fin 5) : GNC.CircularRendezvous.lift initial i = (initialQ i:ℝ) := by
  fin_cases i <;> norm_num [GNC.CircularRendezvous.lift,GNC.CircularRendezvous.radius,
    initial,initialQ,Matrix.cons_val_two,Matrix.cons_val_three]

structure Plan where
  steps : Fin 12 → BoxStep 5
  controls : Fin 12 → Fin 2 → ℚ
  valid : ∀ j, (steps j).Valid (GNC.CircularRendezvous.field (controls j 0) (controls j 1))
  joins : ∀ j : Fin 11, (steps j.castSucc).Compatible (steps j.succ)
  durations : ∀ j, (steps j).duration = 1/20
  first : ∀ i, evaluate ((steps 0).coefficients i) 0 = initialQ i
  prediction : Fin 5 → ℚ
  positionLimit : ℚ
  velocityLimit : ℚ
  budget : Budget (steps 11) prediction positionLimit velocityLimit

def index (j : ℕ) : Fin 12 := ⟨j%12,Nat.mod_lt _ (by norm_num)⟩
def Plan.sequence (P : Plan) (j : ℕ) : BoxStep 5 := P.steps (index j)
def Plan.command (P : Plan) (j : ℕ) : Fin 2 → ℚ := P.controls (index j)

theorem Plan.elapsed (P : Plan) : (∑ j : Fin 12, (P.steps j).duration) = (3/5:ℚ) := by
  simp_rw [P.durations]
  norm_num

theorem Plan.terminal (P : Plan)
    (w : ℕ → ℝ → Fin 4 → ℝ) (hw : ∀ j < 12, Continuous (w j))
    (hr : ∀ j < 12, ∀ t, 0 < GNC.CircularRendezvous.radius (w j t))
    (hd : ∀ j < 12, ∀ t ∈ Set.Icc (0:ℝ) (P.sequence j).duration,
      HasDerivAt (w j) (GNC.CircularRendezvous.physicalRate
        (P.command j 0) (P.command j 1) (w j t)) t)
    (hjw : ∀ j, j+1 < 12 → w (j+1) 0 = w j (P.sequence j).duration)
    (hi : w 0 0 = initial) :
    positionError (GNC.CircularRendezvous.lift (w 11 (P.sequence 11).duration)) P.prediction ≤ (P.positionLimit:ℝ) ∧
    velocityError (GNC.CircularRendezvous.lift (w 11 (P.sequence 11).duration)) P.prediction ≤ (P.velocityLimit:ℝ) := by
  apply physical_segments_bound P.sequence P.command 12 (by norm_num)
  · intro j _
    exact P.valid (index j)
  · intro j hj
    have hj0 : j < 12 := by omega
    have hn : j+1 < 12 := hj
    simpa [Plan.sequence,index,Nat.mod_eq_of_lt hj0,Nat.mod_eq_of_lt hn] using P.joins ⟨j,by omega⟩
  · exact hw
  · exact hr
  · exact hd
  · exact hjw
  · intro i
    rw [hi,initial_lift]
    have hcurve : curve (P.sequence 0).coefficients 0 i = (initialQ i:ℝ) := by
      rw [show (0:ℝ) = ((0:ℚ):ℝ) by norm_num,curve_rational]
      exact congrArg (Rat.cast : ℚ → ℝ) (P.first i)
    rw [hcurve,sub_self,abs_zero]
    exact_mod_cast (P.valid 0).2 i |>.2.1
  · exact P.budget

end GNC.Applications.Rendezvous.EndpointMission
