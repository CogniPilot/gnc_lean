import GNC.Lie.ZeroAttitude
import GNC.Dynamics.GravityLinearization

/-! Exact log-coordinate dynamics from differentiable matrix trajectories.
The exponential differential and commutator transport are proved here; no
Jacobian transport identity is supplied as a hypothesis. -/
noncomputable section
open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GNC

theorem exp_commutator_fderiv (A T : Mat5) :
    fderiv ℝ exp A (A*T-T*A) = exp A*T-T*exp A := by
  have hd : HasDerivAt (MixedInvariant.flow (-T) T A) (A*T-T*A) 0 := by
    convert MixedInvariant.flow_derivative (-T) T A 0 using 1
    rw [MixedInvariant.flow_initial]; noncomm_ring
  have he : HasFDerivAt exp (fderiv ℝ exp A) (MixedInvariant.flow (-T) T A 0) := by
    rw [MixedInvariant.flow_initial]
    exact (NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) A
      (by simp [NormedSpace.expSeries_radius_eq_top])).differentiableAt.hasFDerivAt
  have hf : (fun s => exp (MixedInvariant.flow (-T) T A s)) =
      MixedInvariant.flow (-T) T (exp A) := by
    funext s
    let U : Mat5ˣ := ⟨exp (s • (-T)), exp (s • T),
      by simpa using MixedInvariant.exp_cancel' (s • T),
      by simpa using MixedInvariant.exp_cancel (s • T)⟩
    exact NormedSpace.exp_units_conj U A
  have h := he.comp_hasDerivAt 0 hd
  change HasDerivAt (fun s => exp (MixedInvariant.flow (-T) T A s)) _ 0 at h
  rw [hf] at h
  have hg : HasDerivAt (MixedInvariant.flow (-T) T (exp A)) (exp A*T-T*exp A) 0 := by
    convert MixedInvariant.flow_derivative (-T) T (exp A) 0 using 1
    rw [MixedInvariant.flow_initial]; noncomm_ring
  exact h.unique hg

theorem exp_fderiv_hat (x y : LogState) :
    fderiv ℝ exp (hat x) (hat y) = hat (Jacobian.blockLeft x y)*exp (hat x) := by
  have hE := (NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) (hat x)
    (by simp [NormedSpace.expSeries_radius_eq_top])).differentiableAt
  have hh : HasDerivAt (fun s : ℝ => hat (x+s • y)) (hat y) 0 := by
    have hp : HasDerivAt (fun s : ℝ => x+s • y) y 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const y).const_add x
    exact hatLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hp
  have hE' : HasFDerivAt exp (fderiv ℝ exp (hat x)) (hat (x+(0:ℝ) • y)) := by
    simpa using hE.hasFDerivAt
  exact (hE'.comp_hasDerivAt 0 hh).unique (matrixExp_affine_derivative_all x y)

def logDrift (ν x : LogState) : LogState := ![x 1,0,0]-ad ν x

theorem hat_logDrift (ν x : LogState) :
    hat (logDrift ν x) = hat x*(hat ν+kinematicC)-(hat ν+kinematicC)*hat x := by
  change hatLinear (![x 1,0,0]-ad ν x) = _
  rw [map_sub]
  change hat (![x 1,0,0])-hat (ad ν x) = _
  rw [hat_kinematic, hat_ad, Ring.lie_def, Ring.lie_def]
  noncomm_ring

/-- The group-affine part transports exactly to its linear log drift. -/
theorem logDrift_differential (ν x : LogState) :
    hat (Jacobian.blockLeft x (logDrift ν x))*exp (hat x) =
      exp (hat x)*(hat ν+kinematicC)-(hat ν+kinematicC)*exp (hat x) := by
  rw [← exp_fderiv_hat x (logDrift ν x), hat_logDrift, exp_commutator_fderiv]

theorem blockLeft_add (x y z : LogState) :
    Jacobian.blockLeft x (y+z) = Jacobian.blockLeft x y + Jacobian.blockLeft x z := by
  apply hat_injective
  have h : hat (Jacobian.blockLeft x (y+z))*exp (hat x) =
      hat (Jacobian.blockLeft x y + Jacobian.blockLeft x z)*exp (hat x) := by
    change _ = hatLinear _ * _
    rw [map_add, Matrix.add_mul]
    change _ = hat (Jacobian.blockLeft x y)*exp (hat x)+hat (Jacobian.blockLeft x z)*exp (hat x)
    rw [← exp_fderiv_hat x (y+z), ← exp_fderiv_hat x y,
      ← exp_fderiv_hat x z]
    change (fderiv ℝ exp (hat x)) (hatLinear (y+z)) = _
    rw [map_add, map_add]; rfl
  have hc := congrArg (fun Z => Z*exp (-hat x)) h
  simpa only [Matrix.mul_assoc, MixedInvariant.exp_cancel, Matrix.mul_one] using hc

/-- The inverse differential for a differentiable log-coordinate curve. -/
theorem log_curve_derivative {x : ℝ → LogState} {y u : LogState} {t : ℝ}
    (hx : HasDerivAt x y t) (hqπ : enorm (x t 2) < 2*Real.pi)
    (hE : HasDerivAt (fun s => exp (hat (x s))) (hat u*exp (hat (x t))) t) :
    y = Jacobian.blockInverse (x t) u := by
  have h := (matrixExp_curve_derivative_all hx).unique hE
  have hc := congrArg (fun Z => Z*exp (-hat (x t))) h
  simp only [Matrix.mul_assoc, MixedInvariant.exp_cancel, Matrix.mul_one] at hc
  have hv := hat_injective hc
  have hi := congrArg (Jacobian.blockInverse (x t)) hv
  simpa only [Jacobian.blockInverse_left_all (x t) y hqπ] using hi

/-- Exact log equation, with a left-trivialized input/gravity forcing u. -/
theorem log_error_equation {x : ℝ → LogState} {y ν u : LogState} {t : ℝ}
    (hx : HasDerivAt x y t) (hqπ : enorm (x t 2) < 2*Real.pi)
    (hE : HasDerivAt (fun s => exp (hat (x s)))
      (exp (hat (x t))*(hat ν+kinematicC)-(hat ν+kinematicC)*exp (hat (x t))+
        hat u*exp (hat (x t))) t) :
    y = logDrift ν (x t) + Jacobian.blockInverse (x t) u := by
  have hJ : Jacobian.blockLeft (x t)
      (logDrift ν (x t)+Jacobian.blockInverse (x t) u) =
      Jacobian.blockLeft (x t) (logDrift ν (x t)) + u := by
    rw [blockLeft_add, Jacobian.blockLeft_inverse_all _ _ hqπ]
  have he : HasDerivAt (fun s => exp (hat (x s)))
      (hat (Jacobian.blockLeft (x t) (logDrift ν (x t)+Jacobian.blockInverse (x t) u))*
        exp (hat (x t))) t := by
    rw [hJ]
    change HasDerivAt _ (hatLinear _ * _) _
    rw [map_add, Matrix.add_mul]
    change HasDerivAt _ (hat (Jacobian.blockLeft _ _)*_+_) _
    rw [logDrift_differential ν (x t)]
    exact hE
  have hh := log_curve_derivative hx hqπ he
  simpa only [Jacobian.blockInverse_left_all _ _ hqπ] using hh

end GNC
