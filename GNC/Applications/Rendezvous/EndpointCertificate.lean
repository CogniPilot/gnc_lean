import GNC.Analysis.PolynomialSegments
import GNC.Dynamics.CircularRendezvous

/-! Checked conversion from a polynomial endpoint enclosure to SI rendezvous
position and inertial-velocity error. Limits and endpoint predictions are
explicit rationals; the gravitational speed scale is used exactly squared.
-/
noncomputable section
namespace GNC.Applications.Rendezvous.EndpointCertificate
open GNC.PolynomialODE GNC.Planning.PolynomialKernel

def center (s : BoxStep 5) (i : Fin 5) : ℚ := evaluate (s.coefficients i) s.duration
def coordinateBudget (s : BoxStep 5) (prediction : Fin 5 → ℚ) (i : Fin 5) : ℚ :=
  |center s i-prediction i|+s.error i

def Budget (s : BoxStep 5) (prediction : Fin 5 → ℚ) (position velocity : ℚ) : Prop :=
  let b := coordinateBudget s prediction
  0 ≤ position ∧ 0 ≤ velocity ∧ (∀ i, 0 ≤ b i) ∧
    7000000^2*(b 0^2+b 1^2) ≤ position^2 ∧
    (398600441800000/7000000)*((b 2+b 1)^2+(b 3+b 0)^2) ≤ velocity^2

instance (s : BoxStep 5) (prediction : Fin 5 → ℚ) (position velocity : ℚ) :
    Decidable (Budget s prediction position velocity) := by
  unfold Budget
  infer_instance

def positionError (x : Fin 5 → ℝ) (prediction : Fin 5 → ℚ) : ℝ :=
  7000000*Real.sqrt ((x 0-prediction 0)^2+(x 1-prediction 1)^2)

def velocityError (x : Fin 5 → ℝ) (prediction : Fin 5 → ℚ) : ℝ :=
  Real.sqrt ((398600441800000/7000000)*
    (((x 2-prediction 2)-(x 1-prediction 1))^2+
      ((x 3-prediction 3)+(x 0-prediction 0))^2))

theorem budget_sound (s : BoxStep 5) (prediction : Fin 5 → ℚ) (p v : ℚ)
    (hb : Budget s prediction p v) (x : Fin 5 → ℝ)
    (hx : ∀ i, |x i-curve s.coefficients s.duration i| ≤ (s.error i:ℝ)) :
    positionError x prediction ≤ (p:ℝ) ∧ velocityError x prediction ≤ (v:ℝ) := by
  obtain ⟨hp,hv,hbn,hbp,hbv⟩ := hb
  let b := fun i => (coordinateBudget s prediction i:ℝ)
  let d := fun i => x i-(prediction i:ℝ)
  have hbound (i : Fin 5) : |d i| ≤ b i := by
    have hi := hx i
    rw [curve_rational] at hi
    have ht := abs_sub_le (x i) (center s i:ℝ) (prediction i:ℝ)
    simp only [coordinateBudget,Rat.cast_add,Rat.cast_abs,Rat.cast_sub,b]
    dsimp [d]
    change |x i-(center s i:ℝ)| ≤ (s.error i:ℝ) at hi
    linarith
  have hpos (i : Fin 5) : d i^2 ≤ b i^2 := by
    have hi := hbound i
    nlinarith [sq_abs (d i),abs_nonneg (d i),show 0 ≤ b i by dsimp [b]; exact_mod_cast hbn i]
  have hv0 : (d 2-d 1)^2 ≤ (b 2+b 1)^2 := by
    have ha := abs_sub (d 2) (d 1)
    have hh : |d 2-d 1| ≤ b 2+b 1 := ha.trans (add_le_add (hbound 2) (hbound 1))
    nlinarith [sq_abs (d 2-d 1),abs_nonneg (d 2-d 1)]
  have hv1 : (d 3+d 0)^2 ≤ (b 3+b 0)^2 := by
    have hh := (abs_add_le (d 3) (d 0)).trans (add_le_add (hbound 3) (hbound 0))
    nlinarith [sq_abs (d 3+d 0),abs_nonneg (d 3+d 0)]
  have hp' : (0:ℝ) ≤ p := by exact_mod_cast hp
  have hv' : (0:ℝ) ≤ v := by exact_mod_cast hv
  have hbp' : (7000000:ℝ)^2*(b 0^2+b 1^2) ≤ (p:ℝ)^2 := by
    dsimp [b]
    exact_mod_cast hbp
  have hbv' : (398600441800000/7000000:ℝ)*((b 2+b 1)^2+(b 3+b 0)^2) ≤ (v:ℝ)^2 := by
    dsimp [b]
    have hcast := (Rat.cast_le (K := ℝ)).2 hbv
    push_cast at hcast
    norm_num at hcast ⊢
    exact hcast
  constructor
  · have hs := Real.sq_sqrt (add_nonneg (sq_nonneg (d 0)) (sq_nonneg (d 1)))
    change 7000000*Real.sqrt (d 0^2+d 1^2) ≤ (p:ℝ)
    nlinarith [hpos 0,hpos 1,Real.sqrt_nonneg (d 0^2+d 1^2)]
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨hv',?_⟩
    change (398600441800000/7000000:ℝ)*((d 2-d 1)^2+(d 3+d 0)^2) ≤ (v:ℝ)^2
    nlinarith

/-- All derivative and initial-state hypotheses describe the physical
inverse-square motion. Truncation and rounding bounds come from the checked
polynomial data, including every numerical and command junction. -/
theorem physical_segments_bound (S : ℕ → BoxStep 5) (command : ℕ → Fin 2 → ℚ)
    (N : ℕ) (hN : 0 < N)
    (hvalid : ∀ j < N, (S j).Valid (GNC.CircularRendezvous.field (command j 0) (command j 1)))
    (hjoin : ∀ j, j+1 < N → (S j).Compatible (S (j+1)))
    (w : ℕ → ℝ → Fin 4 → ℝ) (hw : ∀ j < N, Continuous (w j))
    (hr : ∀ j < N, ∀ t, 0 < GNC.CircularRendezvous.radius (w j t))
    (hd : ∀ j < N, ∀ t ∈ Set.Icc (0:ℝ) (S j).duration,
      HasDerivAt (w j) (GNC.CircularRendezvous.physicalRate
        (command j 0) (command j 1) (w j t)) t)
    (hjw : ∀ j, j+1 < N → w (j+1) 0 = w j (S j).duration)
    (hi : ∀ i, |GNC.CircularRendezvous.lift (w 0 0) i-curve (S 0).coefficients 0 i| ≤
      ((S 0).initialError i:ℝ))
    (prediction : Fin 5 → ℚ) (p v : ℚ) (hb : Budget (S (N-1)) prediction p v) :
    positionError (GNC.CircularRendezvous.lift (w (N-1) (S (N-1)).duration)) prediction ≤ (p:ℝ) ∧
    velocityError (GNC.CircularRendezvous.lift (w (N-1) (S (N-1)).duration)) prediction ≤ (v:ℝ) := by
  let x := fun j t => GNC.CircularRendezvous.lift (w j t)
  have hx : ∀ j < N, Continuous (x j) := fun j hj =>
    GNC.CircularRendezvous.lift_continuous (hw j hj) (hr j hj)
  have hdx : ∀ j < N, ∀ t ∈ Set.Icc (0:ℝ) (S j).duration,
      HasDerivAt (x j) (fun i =>
        (GNC.CircularRendezvous.field (command j 0) (command j 1) i).value (x j t)) t := by
    intro j hj t ht
    simpa only [GNC.CircularRendezvous.field_correct] using
      GNC.CircularRendezvous.lift_derivative (hd j hj t ht) (hr j hj t)
  have hjx : ∀ j, j+1 < N → x (j+1) 0 = x j (S j).duration := by
    intro j hj
    dsimp [x]
    rw [hjw j hj]
  have he := box_segments_sound S
    (fun j => GNC.CircularRendezvous.field (command j 0) (command j 1)) N
    hvalid hjoin x hx hdx hjx hi
  have hj : N-1 < N := by omega
  have ht : (0:ℝ) ≤ (S (N-1)).duration := by exact_mod_cast (hvalid (N-1) hj).1
  exact budget_sound _ _ _ _ hb _ (fun i => (he (N-1) hj _ ⟨ht,le_rfl⟩ i).le)

end GNC.Applications.Rendezvous.EndpointCertificate
