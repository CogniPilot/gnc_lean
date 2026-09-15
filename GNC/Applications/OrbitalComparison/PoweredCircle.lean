import GNC.Applications.OrbitalComparison.SecondOrderComparison

/-! An analytic powered circular reference for a finite-pointing comparison.
Time is normalized by 600 seconds; positions are in metres. The orthonormal
plane can be embedded in three-dimensional Euclidean space. -/
noncomputable section
open Set GNC.FiniteAngleComparison
open scoped RealInnerProductSpace
namespace GNC.OrbitalComparison.PoweredCircle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Plane (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  x : E
  y : E
  norm_x : ‖x‖ = 1
  norm_y : ‖y‖ = 1
  orthogonal : ⟪x,y⟫ = 0

theorem Plane.orthogonal_rev (B : Plane E) : ⟪B.y,B.x⟫ = 0 := by
  rw [real_inner_comm,B.orthogonal]

def rate : ℝ := 3231/5000
def thrust : ℝ := mu/7000000^2 - (1077/1000000)^2*7000000

def Plane.radial (B : Plane E) (a : ℝ) : E := Real.cos a • B.x+Real.sin a • B.y
def Plane.tangent (B : Plane E) (a : ℝ) : E := -Real.sin a • B.x+Real.cos a • B.y
def Plane.reference (B : Plane E) (t : ℝ) : E := (7000000:ℝ) • B.radial (rate*t)
def Plane.velocity (B : Plane E) (t : ℝ) : E := (7000000*rate) • B.tangent (rate*t)
def Plane.sineForce (B : Plane E) (t : ℝ) : E := thrust • B.tangent (rate*t)
def Plane.cosineForce (B : Plane E) (t : ℝ) : E := -thrust • B.radial (rate*t)
def Plane.force (B : Plane E) (a t : ℝ) : E :=
  thrust • (B.radial (rate*t+a)-B.radial (rate*t))

theorem Plane.norm_combination (B : Plane E) (a b : ℝ) :
    ‖a • B.x+b • B.y‖^2 = a^2+b^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq,B.norm_x,B.norm_y,
    B.orthogonal_rev,B.orthogonal]
  ring

theorem Plane.norm_radial (B : Plane E) (a : ℝ) : ‖B.radial a‖ = 1 := by
  have hh := B.norm_combination (Real.cos a) (Real.sin a)
  have hs := Real.sin_sq_add_cos_sq a
  dsimp [Plane.radial]
  nlinarith [norm_nonneg (Real.cos a • B.x+Real.sin a • B.y)]

theorem Plane.norm_tangent (B : Plane E) (a : ℝ) : ‖B.tangent a‖ = 1 := by
  have hh := B.norm_combination (-Real.sin a) (Real.cos a)
  have hs := Real.sin_sq_add_cos_sq a
  dsimp [Plane.tangent]
  nlinarith [norm_nonneg (-Real.sin a • B.x+Real.cos a • B.y)]

theorem Plane.reference_norm (B : Plane E) (t : ℝ) : ‖B.reference t‖ = 7000000 := by
  simp [Plane.reference,norm_smul,B.norm_radial]

theorem thrust_bounds : (15/1000:ℝ) < thrust ∧ thrust = (Direct.thrust:ℝ) ∧
    (12/1000:ℝ) < thrust*(1-rate^2/2) := by
  norm_num [thrust,rate,mu,Direct.thrust,Direct.gravityParameter,Direct.referenceRadius,Direct.angularSpeed]

theorem Plane.radial_derivative (B : Plane E) {f : ℝ → ℝ} {v t : ℝ}
    (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => B.radial (f s)) (v • B.tangent (f t)) t := by
  convert (hf.cos.smul_const B.x).add (hf.sin.smul_const B.y) using 1
  dsimp [Plane.tangent]
  module

theorem Plane.tangent_derivative (B : Plane E) {f : ℝ → ℝ} {v t : ℝ}
    (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => B.tangent (f s)) (-v • B.radial (f t)) t := by
  convert (hf.sin.neg.smul_const B.x).add (hf.cos.smul_const B.y) using 1
  dsimp [Plane.radial]
  module

/-- The chosen circle solves the physical inverse-square-plus-thrust ODE. -/
theorem Plane.physical_reference (B : Plane E) (t : ℝ) :
    HasDerivAt B.reference (B.velocity t) t ∧
    HasDerivAt B.velocity ((360000:ℝ) •
      (Gravity.field mu (B.reference t)+thrust • B.radial (rate*t))) t := by
  have hd : HasDerivAt (fun s : ℝ => rate*s) rate t := by
    simpa using (hasDerivAt_id t).const_mul rate
  constructor
  · convert (B.radial_derivative hd).const_smul (7000000:ℝ) using 1
    dsimp [Plane.velocity]
    module
  · convert (B.tangent_derivative hd).const_smul (7000000*rate) using 1
    rw [Gravity.field,B.reference_norm]
    dsimp [Plane.reference,thrust,rate]
    match_scalars <;> ring

/-- Exact finite-angle forcing; no expansion or Magnus approximation. -/
theorem Plane.force_decomposition (B : Plane E) (a t : ℝ) :
    B.force a t = Real.sin a • B.sineForce t+(1-Real.cos a) • B.cosineForce t := by
  dsimp [Plane.force,Plane.sineForce,Plane.cosineForce,Plane.radial,Plane.tangent]
  rw [Real.cos_add,Real.sin_add]
  match_scalars <;> ring

theorem Plane.force_norm (B : Plane E) (a t : ℝ) : ‖B.force a t‖ ≤ thrust*|a| := by
  have hs := Real.abs_sin_le_abs (x := a/2)
  have hc := Real.cos_two_mul (a/2)
  have hid := Real.sin_sq_add_cos_sq (a/2)
  have hab : ‖B.radial (rate*t+a)-B.radial (rate*t)‖^2 = 2-2*Real.cos a := by
    have he : B.radial (rate*t+a)-B.radial (rate*t) =
        (Real.cos (rate*t+a)-Real.cos (rate*t)) • B.x+
        (Real.sin (rate*t+a)-Real.sin (rate*t)) • B.y := by
      dsimp [Plane.radial]
      module
    rw [he,B.norm_combination,Real.cos_add,Real.sin_add]
    calc
      _ = (Real.sin (rate*t)^2+Real.cos (rate*t)^2)*
          (Real.sin a^2+Real.cos a^2+1-2*Real.cos a) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq,Real.sin_sq_add_cos_sq]; ring
  have hnorm : ‖B.radial (rate*t+a)-B.radial (rate*t)‖ ≤ |a| := by
    have hsin : (Real.sin (a/2))^2 ≤ (a/2)^2 := by
      nlinarith [sq_abs (Real.sin (a/2)),sq_abs (a/2),abs_nonneg (Real.sin (a/2)),abs_nonneg (a/2)]
    have hh : 2*(a/2) = a := by ring
    rw [hh] at hc
    nlinarith [norm_nonneg (B.radial (rate*t+a)-B.radial (rate*t)),abs_nonneg a,sq_abs a]
  rw [Plane.force,norm_smul,Real.norm_eq_abs,abs_of_pos (lt_trans (by norm_num) thrust_bounds.1)]
  exact mul_le_mul_of_nonneg_left hnorm (lt_trans (by norm_num) thrust_bounds.1).le

theorem Plane.column_forcing (B : Plane E) (t : ℝ) :
    ‖B.sineForce t‖ ≤ (Direct.thrust:ℝ) ∧ ‖B.cosineForce t‖ ≤ (Direct.thrust:ℝ) := by
  have hth := (lt_trans (by norm_num) thrust_bounds.1 : (0:ℝ) < thrust)
  simp only [Plane.sineForce,Plane.cosineForce,norm_smul,Real.norm_eq_abs,
    abs_neg,abs_of_pos hth,B.norm_tangent,B.norm_radial,mul_one]
  exact ⟨thrust_bounds.2.1.le,thrust_bounds.2.1.le⟩

theorem Plane.sine_projection (B : Plane E) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (12/1000:ℝ) ≤ ⟪B.y,B.sineForce t⟫ := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := rate*t)
  have hs : (rate*t)^2 ≤ rate^2 := by
    have hr : 0 ≤ rate := by norm_num [rate]
    have hh : 0 ≤ rate*t ∧ rate*t ≤ rate :=
      ⟨mul_nonneg hr ht.1,by simpa using mul_le_mul_of_nonneg_left ht.2 hr⟩
    exact pow_le_pow_left₀ hh.1 hh.2 2
  have hth := (lt_trans (by norm_num) thrust_bounds.1 : (0:ℝ) < thrust)
  have hh := mul_le_mul_of_nonneg_left (show 1-rate^2/2 ≤ Real.cos (rate*t) by linarith) hth.le
  simp only [Plane.sineForce,Plane.tangent,real_inner_smul_right,inner_add_right]
  simp only [real_inner_self_eq_norm_sq,B.norm_y,B.orthogonal_rev]
  nlinarith [thrust_bounds.2.2]

/-- Actual nonlinear displacement versus the full second-order variational
predictor, for the stated powered reference and constant pointing parameter.
This bounds ideal ODE solutions; numerical evaluation is a separate step. -/
theorem Plane.strict_comparison (B : Plane E)
    (S : LinearResponse B.reference B.sineForce)
    (C : LinearResponse B.reference B.cosineForce)
    (Q : LinearResponse B.reference (hessianForcing B.reference S.p))
    (p v : ℝ → E) (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt v (nonlinearAcceleration (B.reference t) (p t) (B.force (7/20) t)) t)
    (hip : p 0 = 0) (hiv : v 0 = 0) :
    ‖p 1-exactAngle (7/20) (S.p 1) (C.p 1)‖ < 117/1000 ∧
    2 < ‖p 1-taylorTwo (7/20) (S.p 1) (C.p 1) (Q.p 1)‖ ∧
    17*‖p 1-exactAngle (7/20) (S.p 1) (C.p 1)‖ <
      ‖p 1-taylorTwo (7/20) (S.p 1) (C.p 1) (Q.p 1)‖ := by
  let Y := S.combine C (Real.sin (7/20)) (1-Real.cos (7/20))
  have hq : ∀ t ∈ Icc (0:ℝ) 1, (7000000:ℝ) ≤ ‖B.reference t‖ := by
    intro t _
    rw [B.reference_norm]
  have hf : ∀ t ∈ Icc (0:ℝ) 1,
      ‖B.force (7/20) t‖ ≤ (Direct.thrust:ℝ)*(7/20) := by
    intro t _
    have hh := B.force_norm (7/20) t
    rw [thrust_bounds.2.1] at hh
    norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 7/20)] at hh
    exact hh
  have hY : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt Y.v ((360000:ℝ) •
        (Gravity.gradient mu (B.reference t) (Y.p t)+B.force (7/20) t)) t := by
    intro t ht
    rw [B.force_decomposition]
    exact Y.derivative_v t ht
  have hb := exact_forcing_prediction B.reference p v (B.force (7/20)) Y.p Y.v
    hp hv Y.continuous_p Y.continuous_v hq hf hdp hdv Y.derivative_p hY
    hip hiv Y.initial_p Y.initial_v 1 (by constructor <;> norm_num)
  have hS := S.projected_lower B.y B.norm_y hq
    (fun t _ => (B.column_forcing t).1) (fun _ ht => B.sine_projection ht)
  have hC := C.column_bound hq (fun t _ => (B.column_forcing t).2) 1 (by constructor <;> norm_num)
  have hQ := hessian_response_bound S Q hq (fun t _ => (B.column_forcing t).1)
    1 (by constructor <;> norm_num)
  exact ⟨hb.1,finite_angle_separation (p 1) (S.p 1) (C.p 1) (Q.p 1) hS hC.le hQ.le hb.1⟩

end GNC.OrbitalComparison.PoweredCircle
