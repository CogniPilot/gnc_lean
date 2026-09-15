import GNC.Applications.OrbitalComparison.PointingCapFrame
import GNC.Dynamics.ScaledForcedOrbitExistence
import GNC.Dynamics.PolynomialOrbitCertificate
import GNC.Analysis.SphereResponse

/-! Physical orbit existence and uniqueness for reference-RTN pointing caps,
at horizons up to 1200 seconds. The direction has two uncertain transverse
components; it is fixed in reference RTN throughout the burn. -/
noncomputable section
namespace GNC.OrbitalComparison.PointingCapBurn
open SpatialBurn UniformCertificate PointingCapFrame
open Set

def Admissible (σ : ℝ) (x : Fin 3 → ℝ) : Prop :=
  0≤x 2 ∧ x 2≤1 ∧ x 0^2+x 1^2=2*x 2-x 2^2 ∧ x 0^2+x 1^2≤σ^2
def direction (x : Fin 3 → ℝ) : E3 := pack (1-x 2) (x 0) (x 1)

theorem direction_unit {σ : ℝ} {x : Fin 3 → ℝ} (h : Admissible σ x) :
    ‖direction x‖=1 := by
  have hn := pack_norm_sq (1-x 2) (x 0) (x 1)
  change ‖direction x‖^2=_ at hn
  nlinarith [h.2.2.1,norm_nonneg (direction x)]

theorem direction_bound {σ : ℝ} {x : Fin 3 → ℝ} (hσ : 0≤σ) (h : Admissible σ x) :
    ‖direction x-e0‖≤2*σ := by
  have he : direction x-e0=pack (-x 2) (x 0) (x 1) := by
    ext i
    fin_cases i <;> simp [direction,pack_eq,e0]
  rw [he]
  have hn := pack_norm_sq (-x 2) (x 0) (x 1)
  have hc : x 2^2≤x 2 := by nlinarith [h.1,h.2.1]
  nlinarith [h.2.2.1,h.2.2.2,norm_nonneg (pack (-x 2) (x 0) (x 1))]

theorem parameter_bounds {σ : ℝ} {x : Fin 3 → ℝ}
    (hσ : 0≤σ) (hh : σ^2<1) (h : Admissible σ x) :
    |x 0|≤σ ∧ |x 1|≤σ ∧ |x 2|≤σ^2/(2-σ^2) := by
  refine ⟨?_,?_,?_⟩
  · nlinarith [h.2.2.2,sq_nonneg (x 1),sq_abs (x 0),abs_nonneg (x 0)]
  · nlinarith [h.2.2.2,sq_nonneg (x 0),sq_abs (x 1),abs_nonneg (x 1)]
  · rw [abs_of_nonneg h.1]
    exact SphereResponse.cap_depth_bound h.1 h.2.1 hh h.2.2.1 h.2.2.2

structure Motion (α : ℝ) (n : E3) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=reference α 0
  initial_v : v 0=referenceVelocity α 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (physicalAcceleration α n t (p t)) t

theorem reference_continuous (α : ℝ) : Continuous (reference α) :=
  continuous_iff_continuousAt.mpr fun t => (reference_derivative α t).continuousAt
theorem referenceVelocity_continuous (α : ℝ) : Continuous (referenceVelocity α) :=
  continuous_iff_continuousAt.mpr fun t => (referenceVelocity_derivative α t).continuousAt
theorem turn_continuous (α : ℝ) (n : E3) : Continuous (fun t => turn α t n) :=
  continuous_iff_continuousAt.mpr fun t => (turn_derivative α (hasDerivAt_const t n)).continuousAt

theorem exists_motion {α : ℝ} (hα : 0≤α) (hα2 : α≤2) (n : E3)
    (hn : ‖n-e0‖≤1/5) : ∃ X : Motion α n, ∀ t ∈ Icc (0:ℝ) 1,
      (6800000:ℝ)≤‖X.p t‖ := by
  have hsq : α^2≤4 := by nlinarith
  have ht := SpatialFieldCertificate.physical_constants.2.2
  have hs : 0≤scale α := by unfold scale; positivity
  let d := fun t => scale α • ((Direct.thrust:ℝ) • turn α t (n-e0))
  have hd : Continuous d := ((turn_continuous α (n-e0)).const_smul _).const_smul _
  have hforce (t : ℝ) : ‖d t‖≤scale α*(Direct.thrust:ℝ)/5 := by
    simp only [d,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs,abs_of_nonneg ht,turn_norm]
    nlinarith [mul_le_mul_of_nonneg_left hn (mul_nonneg hs ht)]
  obtain ⟨x,hx,hx0,hradius,hderiv⟩ := ForcedOrbitExistence.exists_relative_four_gain
    (μ := mu) (scale := scale α) (r := 6800000) (R := 100000)
    (by norm_num [mu]) hs (by norm_num) (by norm_num) (by
      norm_num [scale,mu,Direct.gravityParameter]
      nlinarith)
    (reference α) d (reference_continuous α) hd
    (by intro t; rw [reference_norm]; norm_num)
    (D := scale α*(Direct.thrust:ℝ)/5) (by positivity) hforce (by
      norm_num [scale,Direct.thrust,Direct.gravityParameter,Direct.referenceRadius,Direct.angularSpeed]
      nlinarith)
  refine ⟨{
    p := fun t => reference α t+(x t).1
    v := fun t => referenceVelocity α t+(x t).2
    continuous_p := (reference_continuous α).add hx.fst
    continuous_v := (referenceVelocity_continuous α).add hx.snd
    initial_p := by simp [hx0]
    initial_v := by simp [hx0]
    derivative_p := fun t ht => (reference_derivative α t).add (hderiv t ht).fst
    derivative_v := ?_ },hradius⟩
  intro t ht
  convert (referenceVelocity_derivative α t).add (hderiv t ht).snd using 1
  dsimp [physicalAcceleration,ForcedOrbitExistence.rate,d]
  simp only [map_sub]
  module

theorem unique_of_region {α : ℝ} (hα : 0≤α) (hα2 : α≤2) (n : E3)
    (X Y : Motion α n) (hradius : ∀ t ∈ Icc (0:ℝ) 1, (6800000:ℝ)≤‖Y.p t‖) :
    ∀ t ∈ Icc (0:ℝ) 1, X.p t=Y.p t ∧ X.v t=Y.v t := by
  have hsq : α^2≤4 := by nlinarith
  have hs : 0≤scale α := by unfold scale; positivity
  have h := Gravity.constant_prediction mu (scale α) (by norm_num [mu]) hs
    X.p X.v Y.p Y.v (fun t => physicalAcceleration α n t (Y.p t))
    (fun t => (Direct.thrust:ℝ) • turn α t n)
    (κ := 4) (F := 0) (r := 6700000) (M := 100000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [scale,mu,Direct.gravityParameter]; nlinarith)
    (by intro t ht; simpa only [show (6700000:ℝ)+100000=6800000 by norm_num] using hradius t ht)
    X.continuous_p X.continuous_v Y.continuous_p Y.continuous_v
    X.derivative_p X.derivative_v Y.derivative_p Y.derivative_v
    (X.initial_p.trans Y.initial_p.symm) (X.initial_v.trans Y.initial_v.symm)
    (by intro t ht; simp [physicalAcceleration])
  intro t ht
  have hp := (h t ht).1
  have hv := (h t ht).2
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using And.intro hp hv

end GNC.OrbitalComparison.PointingCapBurn
