import GNC.Control.PolytopicTube
import GNC.Lie.Euclidean

/-! A certified mechanism benchmark for geometric versus independent-entry
polytopic enclosures. This is rotating-frame transport, not the full aircraft.
Both enclosures analyze the same vector field and physical disturbance.
A Cartesian treatment preserving the skew correlation recovers the exact
same certificate as the geometric treatment.
-/
noncomputable section
open Matrix Real Set
open scoped Matrix
namespace GNC.FlowTubeComparison

def transport (k ω : ℝ) (x : Vec3) : Vec3 :=
  -k • x + (![0, 0, ω] ⨯₃ x)

theorem transport_pairing (k ω : ℝ) (x : Vec3) :
    x ⬝ᵥ transport k ω x = -k * lengthSq x := by
  simp [transport, dotProduct_add, dotProduct_smul, dot_self_lengthSq]

/-- Exact quadratic block-LMI supply, uniform in the angular transport.
The coefficient omega may depend arbitrarily on time and state. -/
theorem transport_supply {k κ : ℝ} (hκ : 0 < κ) (hk : κ ≤ k)
    (ω : ℝ) (x d : Vec3) :
    2 * (x ⬝ᵥ (transport k ω x+d)) + κ * lengthSq x ≤ lengthSq d / κ := by
  have hsq := lengthSq_nonneg (κ • x-d)
  have hprod := mul_nonneg (sub_nonneg.mpr hk) (lengthSq_nonneg x)
  have hid : κ * (2 * (x ⬝ᵥ (transport k ω x+d)) + κ * lengthSq x) =
      lengthSq d-lengthSq (κ • x-d)-2*κ*(k-κ)*lengthSq x := by
    rw [dotProduct_add, transport_pairing]
    simp [lengthSq, dotProduct, Fin.sum_univ_succ]
    ring
  apply (le_div_iff₀ hκ).mpr
  rw [mul_comm, hid]
  nlinarith [mul_nonneg hκ.le hprod]

/-- Exact log-attitude nonlinearity from the backstepping model is invisible
to its isotropic attitude energy. This does not hold for arbitrary metrics. -/
theorem inverseJacobian_residual_neutral (q z : Vec3) :
    q ⬝ᵥ (Jacobian.inverseAt (-q) z-z) = 0 := by
  rw [dotProduct_sub, LogBackstepping.inverse_right_radial_pairing]
  ring

def entryVertex (k a b : ℝ) (x : Vec3) : Vec3 :=
  ![-k*x 0+a*x 1, b*x 0-k*x 1, -k*x 2]

theorem transport_is_correlated_vertex (k ω : ℝ) (x : Vec3) :
    transport k ω x = entryVertex k (-ω) ω x := by
  ext i
  fin_cases i <;> simp [transport, entryVertex, crossProduct] <;> ring

/-- An independent-entry interval contains this expanding direction even
though the actual skew transport has no such direction. -/
theorem box_expanding_direction (k Ω : ℝ) :
    entryVertex k Ω Ω ![1,1,0] = (Ω-k) • ![1,1,0] := by
  ext i
  fin_cases i <;> simp [entryVertex] <;> ring

/-- No positive quadratic metric can make the enlarged interval polytope
strictly contracting when Omega >= k. The claim is about the enclosure,
not instability of the actual rotating-frame system. -/
theorem no_contracting_metric_on_box {k Ω α : ℝ} (hΩ : k ≤ Ω) (hα : 0 < α)
    (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : 0 < (![1,1,0] : Vec3) ⬝ᵥ (P *ᵥ ![1,1,0])) :
    ¬ (2 * ((![1,1,0] : Vec3) ⬝ᵥ (P *ᵥ entryVertex k Ω Ω ![1,1,0])) +
      α * ((![1,1,0] : Vec3) ⬝ᵥ (P *ᵥ ![1,1,0])) ≤ 0) := by
  rw [box_expanding_direction, Matrix.mulVec_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  have h := mul_nonneg (sub_nonneg.mpr hΩ) hP.le
  have ha := mul_pos hα hP
  linarith

/-- Independent entry bounds lose at most Omega in this isotropic metric.
This bound is attained by the spurious expanding vertex above. -/
theorem entry_bound {a b Ω : ℝ} (ha : |a| ≤ Ω) (hb : |b| ≤ Ω)
    (k : ℝ) (x : Vec3) :
    x ⬝ᵥ entryVertex k a b x ≤ -(k-Ω)*lengthSq x := by
  have hΩ : 0 ≤ Ω := (abs_nonneg a).trans ha
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hmul : (a+b)*x 0*x 1 ≤ Ω*((x 0)^2+(x 1)^2) := by
    by_cases h : 0 ≤ x 0*x 1
    · have h' := mul_le_mul_of_nonneg_right (add_le_add ha'.2 hb'.2) h
      nlinarith [mul_nonneg hΩ (sq_nonneg (x 0-x 1))]
    · have h' := mul_le_mul_of_nonpos_right (add_le_add ha'.1 hb'.1) (le_of_not_ge h)
      nlinarith [mul_nonneg hΩ (sq_nonneg (x 0+x 1))]
  simp [entryVertex, dotProduct, Fin.sum_univ_succ, lengthSq]
  nlinarith [mul_nonneg hΩ (sq_nonneg (x 2))]

/-- Young's exact sum-of-squares certificate, including noncontracting
finite-horizon enclosures. No optimization or floating-point oracle is used. -/
theorem supply_of_pairing {κ η : ℝ} (hη : 0 < η) (x f d : Vec3)
    (hf : x ⬝ᵥ f ≤ -κ*lengthSq x) :
    2*(x ⬝ᵥ (f+d))+(2*κ-η)*lengthSq x ≤ lengthSq d/η := by
  have hsq := lengthSq_nonneg (η • x-d)
  have hid : lengthSq (η • x-d) =
      η^2*lengthSq x-2*η*(x ⬝ᵥ d)+lengthSq d := by
    simp [lengthSq, dotProduct, Fin.sum_univ_succ]
    ring
  rw [hid] at hsq
  apply (le_div_iff₀ hη).mpr
  rw [dotProduct_add]
  nlinarith [mul_le_mul_of_nonneg_left hf hη.le]

theorem entry_supply {a b Ω η : ℝ} (ha : |a| ≤ Ω) (hb : |b| ≤ Ω)
    (hη : 0 < η) (k : ℝ) (x d : Vec3) :
    2*(x ⬝ᵥ (entryVertex k a b x+d))+(2*(k-Ω)-η)*lengthSq x ≤
      lengthSq d/η :=
  supply_of_pairing hη x _ d (entry_bound ha hb k x)

/-- Smooth state-dependent skew transport dissipates energy everywhere,
yet two specific states violate Euclidean incremental contraction. This
does not rule out a different metric or contraction on a smaller region. -/
theorem energy_decay_is_not_incremental_contraction :
    (∀ x : Vec3, x ⬝ᵥ transport 1 (2*x 1) x = -lengthSq x) ∧
    0 < ((![1,1,0] : Vec3)-![1,0,0]) ⬝ᵥ
      (transport 1 2 ![1,1,0]-transport 1 0 ![1,0,0]) := by
  constructor
  · intro x
    simpa using transport_pairing 1 (2*x 1) x
  · norm_num [transport, dotProduct, crossProduct, Fin.sum_univ_succ, Matrix.cons_val]
    norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- Concrete counterexample to checking the smallest eigenvalue for a
negative-semidefinite LMI: diag(-1,1) has a negative direction and a positive
direction. A negative smallest eigenvalue alone does not certify the LMI. -/
theorem negative_direction_is_not_nsd :
    (-1 : ℝ)*1^2+1*0^2 < 0 ∧ ¬ ((-1 : ℝ)*0^2+1*1^2 ≤ 0) := by norm_num

/-- The Schur-complement supply term has a positive sign. A minus-sign
test accepts this example, while the actual block quadratic form is positive. -/
theorem wrong_schur_sign_counterexample :
    (-1 : ℝ)-2^2/1 < 0 ∧
    0 < (-1 : ℝ)*1^2+2*2*1*1+(-1)*1^2 := by norm_num

/-- The benchmark bounds apply to actual differentiable trajectories,
including arbitrary time-varying transport and bounded disturbances. -/
theorem trajectory_tube {x f d : ℝ → Vec3} {κ η δ a b t : ℝ}
    (hη : 0 < η) (hα : 2*κ-η ≠ 0)
    (hx : ∀ s ∈ Icc a b, HasDerivAt x (f s+d s) s)
    (hf : ∀ s ∈ Ico a b, x s ⬝ᵥ f s ≤ -κ*lengthSq (x s))
    (hd : ∀ s ∈ Ico a b, lengthSq (d s) ≤ δ^2)
    (ht : t ∈ Icc a b) :
    lengthSq (x t) ≤ lengthSq (x a)*exp (-(2*κ-η)*(t-a))+
      ((δ^2/η)/(2*κ-η))*(1-exp (-(2*κ-η)*(t-a))) := by
  apply Lyapunov.disturbed_bound_on
    (V := fun s => lengthSq (x s))
    (dV := fun s => 2*(x s ⬝ᵥ (f s+d s))) hα _ _ t ht
  · intro s hs
    exact LogBackstepping.lengthSq_derivative (hx s hs)
  · intro s hs
    have h := supply_of_pairing hη (x s) (f s) (d s) (hf s hs)
    have hb := div_le_div_of_nonneg_right (hd s hs) hη.le
    dsimp only
    linarith

/-- Lift the actual-trajectory certificate to every admitted initial state
and disturbance. Existence and regional validity remain explicit. -/
theorem pairing_reachable_tube (valid : (ℝ → Vec3) → Prop)
    {κ η δ ρ a b t : ℝ} (hη : 0 < η) (hα : 2*κ-η ≠ 0)
    (hvalid : ∀ x, valid x → ∃ f d : ℝ → Vec3,
      (∀ s ∈ Icc a b, HasDerivAt x (f s+d s) s) ∧
      (∀ s ∈ Ico a b, x s ⬝ᵥ f s ≤ -κ*lengthSq (x s)) ∧
      (∀ s ∈ Ico a b, lengthSq (d s) ≤ δ^2))
    (ht : t ∈ Icc a b) :
    Reachability.reachable valid (Reachability.sublevel lengthSq ρ) a t ⊆
      Reachability.sublevel lengthSq
        (ρ*exp (-(2*κ-η)*(t-a))+
          ((δ^2/η)/(2*κ-η))*(1-exp (-(2*κ-η)*(t-a)))) := by
  apply Reachability.sublevel_enclosure _ _ (exp_pos _).le
  intro x hx
  obtain ⟨f,d,hder,hpair,hdis⟩ := hvalid x hx
  exact trajectory_tube hη hα hder hpair hdis ht

end GNC.FlowTubeComparison
