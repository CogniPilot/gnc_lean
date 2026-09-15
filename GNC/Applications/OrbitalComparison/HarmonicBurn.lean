import GNC.Applications.OrbitalComparison.SpatialExistence
import GNC.Analysis.HarmonicPointing
import GNC.Analysis.HarmonicPolynomial
import GNC.Dynamics.OrbitalCertificate
import GNC.Analysis.PolynomialSupersolution

/-! A prescribed oscillating pointing law, retaining the exact reference
rotation and the full inverse-square physical field.  The unknown phase is
arbitrary. The amplitude is the stated fixed rational value, not an entire
interval of amplitudes. No attitude-controller realization is assumed. -/
noncomputable section
namespace GNC.OrbitalComparison.HarmonicBurn
open Set Real SpatialBurn SpatialRotatingFrame SpatialExactNominal SpatialFieldCertificate
open UniformCertificate
open scoped RealInnerProductSpace

def amplitude : ℚ := 11/630
def phase (ω φ t : ℝ) : ℝ := ω*t+φ
def pointing (ω φ t : ℝ) : ℝ := (amplitude:ℝ)*sin (phase ω φ t)
def source (ω φ t : ℝ) : E3 :=
  SpatialBurn.source .rtnReferenceOffset (pointing ω φ t) t
def acceleration (ω φ t : ℝ) (p : E3) : E3 :=
  (360000:ℝ) • (Gravity.field mu p+(Direct.thrust:ℝ) • source ω φ t)

structure Motion (ω φ : ℝ) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0 = nominal.p 0
  initial_v : v 0 = nominal.v 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (acceleration ω φ t (p t)) t

theorem source_continuous (ω φ : ℝ) : Continuous (source ω φ) := by
  have he : source ω φ = fun t =>
      mix ((omega:ℝ)*t) (cos (pointing ω φ t))
        ((4/5)*sin (pointing ω φ t)) ((3/5)*sin (pointing ω φ t)) :=
    funext fun t => rtn_source (pointing ω φ t) t
  rw [he]
  dsimp [mix,pack,pointing,phase]
  fun_prop

theorem source_unit (ω φ t : ℝ) : ‖source ω φ t‖ = 1 :=
  SpatialBurn.source_unit _ _ _

def input (ω φ t : ℝ) : E3 := (360000:ℝ) • ((Direct.thrust:ℝ) •
  (source ω φ t-SpatialBurn.source .rtnReferenceOffset 0 t))

theorem input_bound (ω φ t : ℝ) : ‖input ω φ t‖ ≤ 720000*(Direct.thrust:ℝ) := by
  have ht : (0:ℝ) ≤ Direct.thrust := SpatialFieldCertificate.physical_constants.2.2
  have h := norm_sub_le (source ω φ t) (SpatialBurn.source .rtnReferenceOffset 0 t)
  rw [source_unit,SpatialBurn.source_unit] at h
  rw [input,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 360000),abs_of_nonneg ht]
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num : (0:ℝ) ≤ 360000) ht)]

theorem exists_motion (ω φ : ℝ) : ∃ X : Motion ω φ, ∀ t ∈ Icc (0:ℝ) 1,
    (6800000:ℝ) ≤ ‖X.p t‖ := by
  have hc : Continuous (input ω φ) :=
    (((source_continuous ω φ).sub (SpatialExistence.source_continuous .rtnReferenceOffset 0)).const_smul
      (Direct.thrust:ℝ)).const_smul (360000:ℝ)
  obtain ⟨x,hx,hx0,_,hradius,hderiv⟩ := ForcedOrbitExistence.exists_relative
    (μ := mu) (scale := 360000) (r := 6800000) (R := 100000)
    (by norm_num [mu]) (by norm_num) (by norm_num) (by norm_num) (by norm_num [mu])
    nominal.p (input ω φ) nominal.continuous_p hc
    (by intro t; rw [nominal_norm]; norm_num)
    (D := 720000*(Direct.thrust:ℝ))
    (mul_nonneg (by norm_num) SpatialFieldCertificate.physical_constants.2.2)
    (input_bound ω φ) (by
      norm_num [Direct.thrust,Direct.gravityParameter,Direct.referenceRadius,Direct.angularSpeed])
  refine ⟨{
    p := fun t => nominal.p t+(x t).1
    v := fun t => nominal.v t+(x t).2
    continuous_p := nominal.continuous_p.add hx.fst
    continuous_v := nominal.continuous_v.add hx.snd
    initial_p := by simp [hx0]
    initial_v := by simp [hx0]
    derivative_p := fun t ht => (nominal.derivative_p t ht).add (hderiv t ht).fst
    derivative_v := ?_ },hradius⟩
  intro t ht
  convert (nominal.derivative_v t ht).add (hderiv t ht).snd using 1
  dsimp [acceleration,ForcedOrbitExistence.rate,physicalAcceleration,input]
  module

def trajectory (ω φ : ℝ) : Motion ω φ := Classical.choose (exists_motion ω φ)

theorem trajectory_unique (ω φ : ℝ) (X : Motion ω φ) :
    ∀ t ∈ Icc (0:ℝ) 1, X.p t = (trajectory ω φ).p t ∧ X.v t = (trajectory ω φ).v t := by
  let Y := trajectory ω φ
  apply ForcedOrbitUniqueness.unique mu 360000 (by norm_num [mu]) (by norm_num)
    X.p X.v Y.p Y.v (fun t => (Direct.thrust:ℝ) • source ω φ t)
    X.continuous_p X.continuous_v Y.continuous_p Y.continuous_v
    X.derivative_p X.derivative_v Y.derivative_p Y.derivative_v
    (X.initial_p.trans Y.initial_p.symm) (X.initial_v.trans Y.initial_v.symm)
    (r := 6700000) (M := 100000) (by norm_num) (by norm_num) (by norm_num [mu])
  intro t ht
  simpa only [Y,trajectory,show (6700000:ℝ)+100000 = 6800000 by norm_num]
    using Classical.choose_spec (exists_motion ω φ) t ht

end GNC.OrbitalComparison.HarmonicBurn
