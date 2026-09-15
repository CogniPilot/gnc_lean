import GNC.Dynamics.ForcedOrbitExistence
import GNC.Dynamics.ForcedOrbitUniqueness
import GNC.Applications.OrbitalComparison.SpatialExactNominal

/-! Construct the spatial benchmark's physical orbits, without assuming
a solution or noncollision. All three prescribed thrust laws and every
real angle are covered. The coarse enclosure constructs solutions only;
the checked predictor coefficients supply their independent sharp bounds. -/
noncomputable section
namespace GNC.OrbitalComparison.SpatialExistence
open Set SpatialBurn SpatialFieldCertificate SpatialExactNominal
open UniformCertificate

theorem source_continuous (mode : Law) (θ : ℝ) :
    Continuous (SpatialBurn.source mode θ) := by
  have he : SpatialBurn.source mode θ = fun t =>
      pack ((components mode (Real.cos θ) (Real.sin θ)
        (Real.cos ((omega:ℝ)*t)) (Real.sin ((omega:ℝ)*t))) 0)
      ((components mode (Real.cos θ) (Real.sin θ)
        (Real.cos ((omega:ℝ)*t)) (Real.sin ((omega:ℝ)*t))) 1)
      ((components mode (Real.cos θ) (Real.sin θ)
        (Real.cos ((omega:ℝ)*t)) (Real.sin ((omega:ℝ)*t))) 2) :=
    funext (source_components mode θ)
  rw [he]
  cases mode <;> simp [components, pack, Matrix.cons_val_two] <;> fun_prop

def input (mode : Law) (θ t : ℝ) : E3 :=
  (360000:ℝ) • ((Direct.thrust:ℝ) •
    (SpatialBurn.source mode θ t-SpatialBurn.source .rtnReferenceOffset 0 t))

theorem input_continuous (mode : Law) (θ : ℝ) : Continuous (input mode θ) :=
  (((source_continuous mode θ).sub (source_continuous .rtnReferenceOffset 0)).const_smul
    (Direct.thrust:ℝ)).const_smul (360000:ℝ)

theorem input_bound (mode : Law) (θ t : ℝ) :
    ‖input mode θ t‖ ≤ 720000*(Direct.thrust:ℝ) := by
  have ht : (0:ℝ) ≤ Direct.thrust := physical_constants.2.2
  have h := norm_sub_le (SpatialBurn.source mode θ t) (SpatialBurn.source .rtnReferenceOffset 0 t)
  rw [source_unit,source_unit] at h
  rw [input,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 360000),abs_of_nonneg ht]
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num : (0:ℝ) ≤ 360000) ht)]

/-- The field is extended only outside a 100 km error box. The entire
constructed solution stays inside it, for every pointing angle; no angle
smallness hypothesis or unknown trajectory radius is supplied. -/
theorem exists_noncolliding (mode : Law) (θ : ℝ) :
    ∃ X : PhysicalOrbit mode θ, ∀ t ∈ Icc (0:ℝ) 1,
      (6800000:ℝ) ≤ ‖X.p t‖ ∧
      ‖X.p t-nominal.p t‖ ≤ 2880000*(Direct.thrust:ℝ) ∧
      ‖X.v t-nominal.v t‖ ≤ 2880000*(Direct.thrust:ℝ) := by
  obtain ⟨x,hx,hx0,hbound,hradius,hderiv⟩ := ForcedOrbitExistence.exists_relative
    (μ := mu) (scale := 360000) (r := 6800000) (R := 100000)
    (by norm_num [mu]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mu])
    nominal.p (input mode θ) nominal.continuous_p (input_continuous mode θ)
    (by intro t; rw [nominal_norm]; norm_num)
    (D := 720000*(Direct.thrust:ℝ))
    (mul_nonneg (by norm_num) physical_constants.2.2)
    (input_bound mode θ) (by
      norm_num [Direct.thrust,Direct.gravityParameter,Direct.referenceRadius,Direct.angularSpeed])
  let p : ℝ → E3 := fun t => nominal.p t+(x t).1
  let v : ℝ → E3 := fun t => nominal.v t+(x t).2
  have hdp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt p (v t) t :=
    (nominal.derivative_p t ht).add (hderiv t ht).fst
  have hdv (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt v (physicalAcceleration mode θ t (p t)) t := by
    have h := (nominal.derivative_v t ht).add (hderiv t ht).snd
    convert h using 1
    dsimp [v,p,ForcedOrbitExistence.rate,physicalAcceleration,input]
    module
  let X : PhysicalOrbit mode θ := {
    p := p
    v := v
    continuous_p := nominal.continuous_p.add hx.fst
    continuous_v := nominal.continuous_v.add hx.snd
    initial_p := by simpa only [p,hx0,Prod.fst_zero,add_zero] using nominal.initial_p
    initial_v := by simpa only [v,hx0,Prod.snd_zero,add_zero] using nominal.initial_v
    derivative_p := hdp
    derivative_v := hdv }
  refine ⟨X,fun t ht => ⟨hradius t ht,?_,?_⟩⟩
  · simpa only [X,p,add_sub_cancel_left,← mul_assoc,show (4:ℝ)*720000 = 2880000 by norm_num]
      using (norm_fst_le (x t)).trans (hbound t ht)
  · simpa only [X,v,add_sub_cancel_left,← mul_assoc,show (4:ℝ)*720000 = 2880000 by norm_num]
      using (norm_snd_le (x t)).trans (hbound t ht)

theorem exists_motion (mode : Law) (θ : ℝ) : Nonempty (PhysicalOrbit mode θ) :=
  let ⟨X,_⟩ := exists_noncolliding mode θ
  ⟨X⟩

/-- A physical trajectory for each parameter, obtained from the existence
theorem rather than supplied as an assumption to a comparison. -/
def trajectory (mode : Law) (θ : ℝ) : PhysicalOrbit mode θ :=
  Classical.choose (exists_noncolliding mode θ)

theorem trajectory_radius (mode : Law) (θ : ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (6800000:ℝ) ≤ ‖(trajectory mode θ).p t‖ :=
  (Classical.choose_spec (exists_noncolliding mode θ) t ht).1

/-- Every supplied solution agrees with the constructed one on the burn.
No proximity or noncollision premise is required of the supplied solution. -/
theorem trajectory_unique (mode : Law) (θ : ℝ) (X : PhysicalOrbit mode θ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      X.p t = (trajectory mode θ).p t ∧ X.v t = (trajectory mode θ).v t := by
  let Y := trajectory mode θ
  apply ForcedOrbitUniqueness.unique mu 360000 (by norm_num [mu]) (by norm_num)
    X.p X.v Y.p Y.v (fun t => (Direct.thrust:ℝ) • SpatialBurn.source mode θ t)
    X.continuous_p X.continuous_v Y.continuous_p Y.continuous_v
    X.derivative_p X.derivative_v Y.derivative_p Y.derivative_v
    (X.initial_p.trans Y.initial_p.symm) (X.initial_v.trans Y.initial_v.symm)
    (r := 6700000) (M := 100000) (by norm_num) (by norm_num)
    (by norm_num [mu])
  intro t ht
  simpa only [Y,show (6700000:ℝ)+100000 = 6800000 by norm_num] using trajectory_radius mode θ ht

end GNC.OrbitalComparison.SpatialExistence
