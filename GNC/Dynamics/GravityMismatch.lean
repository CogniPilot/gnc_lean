import GNC.Dynamics.GravityGradientBound
import GNC.Dynamics.LieErrorReconstruction

/-! Sharp finite-separation inverse-square gravity mismatch, and its
transport to the actual SE₂(3) logarithmic coordinates. This is the bound
in Proposition 1 of the October 2026 spacecraft technical note. It bounds
the full mismatch, not the remainder after retaining the gravity gradient.
The removable zero-attitude case is included explicitly. -/
noncomputable section
namespace GNC.Gravity
open Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def mismatchBound (μ r d : ℝ) : ℝ := μ*d*(2*r-d)/(r^2*(r-d)^2)

theorem mismatchBound_eq (μ r d : ℝ) (hr : r ≠ 0) (hrd : r-d ≠ 0) :
    mismatchBound μ r d = μ/(r-d)^2-μ/r^2 := by
  unfold mismatchBound
  field_simp; ring

theorem mismatchBound_mono (μ r d D : ℝ) (hμ : 0≤μ)
    (hd : 0≤d) (hdD : d≤D) (hDr : D<r) :
    mismatchBound μ r d ≤ mismatchBound μ r D := by
  have hr : 0<r := lt_of_le_of_lt (hd.trans hdD) hDr
  have hrd : 0<r-d := by linarith
  have hrD : 0<r-D := by linarith
  rw [mismatchBound_eq μ r d hr.ne' hrd.ne',
    mismatchBound_eq μ r D hr.ne' hrD.ne']
  apply sub_le_sub_right
  exact div_le_div_of_nonneg_left hμ (by positivity)
    (pow_le_pow_left₀ hrD.le (by linarith) 2)

/-- The actual vector field, rather than an assumed Lipschitz oracle.
The sharp Taylor remainder plus the sharp gradient bound simplifies to
the exact radial mismatch envelope. -/
theorem field_difference_sharp (μ : ℝ) (hμ : 0≤μ) (q v : E)
    (hd : ‖v‖<‖q‖) :
    ‖field μ (q+v)-field μ q‖ ≤ mismatchBound μ ‖q‖ ‖v‖ := by
  have hr : 0<‖q‖ := lt_of_le_of_lt (norm_nonneg v) hd
  have hrd : 0<‖q‖-‖v‖ := by linarith
  have he : field μ (q+v)-field μ q = gradient μ q v +
      (field μ (q+v)-field μ q-gradient μ q v) := by abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (gradient_bound μ hμ q v) (remainder_bound μ hμ q v hd)).trans_eq
  unfold remainderBound mismatchBound
  field_simp; ring

def inverseJacobianGain (θ : ℝ) : ℝ :=
  if θ=0 then 1 else (θ/2)/sin (θ/2)

theorem inverseAt_gain (φ v : Vec3) (hφ : enorm φ<π) :
    enorm (Jacobian.inverseAt φ v) ≤ inverseJacobianGain (enorm φ)*enorm v := by
  by_cases hz : φ=0
  · simp [hz, Jacobian.inverseAt, inverseJacobianGain, enorm]
  · have hθ : 0<enorm φ := lt_of_le_of_ne (enorm_nonneg _) (Ne.symm
      (fun h => hz ((enorm_eq_zero_iff _).mp h)))
    let k := Jacobian.unitAxis φ
    have hk : k ⬝ᵥ k=1 := Jacobian.unitAxis_unit _ hθ
    have he : φ=enorm φ • k := (Jacobian.unitAxis_reconstruct _ hθ).symm
    rw [he, Jacobian.inverseAt_axis k v hk _ hθ]
    have hh := Jacobian.leftInv_bound k v hk (enorm φ) hθ (by linarith [pi_pos])
    simpa only [← he, inverseJacobianGain, if_neg hθ.ne'] using hh

/-- The paper's full gravity bound, including θ=0, for the actual
physical separation R J(φ)ρ and the actual inverse Jacobian. -/
theorem log_mismatch_bound (μ : ℝ) (hμ : 0≤μ) (R : SO3)
    (q ρ φ : Vec3) (hρ : enorm ρ<enorm q) (hφ : enorm φ<π) :
    enorm (Jacobian.inverseAt φ (rotate R⁻¹
      (field3 μ (q+physicalImpulse R φ ρ)-field3 μ q))) ≤
      inverseJacobianGain (enorm φ)*mismatchBound μ (enorm q) (enorm ρ) := by
  have hd : enorm (physicalImpulse R φ ρ)≤enorm ρ := by
    unfold physicalImpulse
    rw [rotate_enorm]
    exact leftAt_nonexpansive φ ρ (by linarith [pi_pos])
  have hf := field_difference_sharp μ hμ (WithLp.toLp 2 q : Jacobian.E3)
    (WithLp.toLp 2 (physicalImpulse R φ ρ)) (hd.trans_lt hρ)
  change enorm (field3 μ (q+physicalImpulse R φ ρ)-field3 μ q) ≤ _ at hf
  have hm := mismatchBound_mono μ (enorm q) (enorm (physicalImpulse R φ ρ))
    (enorm ρ) hμ (enorm_nonneg _) hd hρ
  have hgain : 0 ≤ inverseJacobianGain (enorm φ) := by
    unfold inverseJacobianGain
    split_ifs with hz
    · norm_num
    · have hpos : 0 < enorm φ := lt_of_le_of_ne (enorm_nonneg _) (Ne.symm hz)
      exact div_nonneg (by positivity)
        (sin_pos_of_pos_of_lt_pi (by linarith)
          (by linarith [pi_pos])).le
  have hi := inverseAt_gain φ (rotate R⁻¹
    (field3 μ (q+physicalImpulse R φ ρ)-field3 μ q)) hφ
  rw [rotate_enorm] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (hf.trans hm) hgain)

end GNC.Gravity
