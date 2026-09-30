import GNC.Dynamics.SharedInputLogLift
import GNC.Dynamics.OrbitalApproximateTube

/-! A physical shared-input orbital tube with a constructed log lift.

The inputs and kinematics have continuous extensions to real time; the
inverse-square gravity equations are required only on the certified interval.
The trajectories are existing classical solutions, not assumed close. The
logarithmic error and its continuous derivative are constructed from them.
An approximate propagator is allowed and its defect is charged explicitly.
No exact STM, assumed log lift, or assumed uncertainty tube is required.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace GNC.SharedInputOrbitalTube
open OrbitalLogTube SharedInputLogLift

/-- Physical-to-reachable-set theorem for matched body acceleration and
angular rate, full position-dependent gravity, and an inexact propagator.

`a` bounds the computed linear response, `d` its integrated generator error,
and `b` the integrated quadratic gravity remainder. The closure test is the
quadratic discriminant, with no iteration or extra numerical allowance.
Existence of the physical trajectories and the certified candidate gains
remain hypotheses; this theorem does not assert universal computational
superiority over another coordinate implementation.
-/
theorem certificate (C : Coordinates) (μ : ℝ) (hμ : 0≤μ)
    (X Y : ℝ → SE23) (acc ω gx gy : ℝ → Vec3)
    (hacc : Continuous acc) (hω : Continuous ω)
    (hgx : Continuous gx) (hgy : Continuous gy)
    (hX : ∀ t, SpacecraftODEAt X (acc t) (ω t) (gx t) t)
    (hY : ∀ t, SpacecraftODEAt Y (acc t) (ω t) (gy t) t)
    (φ : Vec3) (hφ : enorm φ < Real.pi)
    (hrot : (X 0).rot = rotationExp φ * (Y 0).rot)
    (Ψ : ℝ → Endˣ) (B : ℝ → End) (e : ℝ → ℝ)
    (initial : Set LogState) {T a d b r D p α w : ℝ}
    (hT : 0≤T) (ha : 0<a) (hd0 : 0≤d) (hd1 : d<1) (hb : 0≤b)
    (hsmall : 4*a*b<(1-d)^2)
    (hp : 0≤p) (hα : 0≤α) (hw : 0≤w)
    (hD : D<r) (hposDomain : p*(2*(a/(1-d)))≤D)
    (hangDomain : α*(2*(a/(1-d)))≤1)
    (hscalep : ∀ z, enorm (C z 0)≤p*‖z‖)
    (hscaleα : ∀ z, enorm (C z 2)≤α*‖z‖)
    (hscalew : ∀ v, ‖C.symm (velocityOnly v)‖≤w*enorm v)
    (hq : ∀ t ∈ Icc 0 T, r≤enorm (Y t).pos)
    (hgX : ∀ t ∈ Icc 0 T, gx t=Gravity.field3 μ (X t).pos)
    (hgY : ∀ t ∈ Icc 0 T, gy t=Gravity.field3 μ (Y t).pos)
    (hB : Continuous B) (hec : Continuous e)
    (he0 : ∀ t ∈ Icc 0 T, 0≤e t)
    (hA : Continuous (fun t => scaledOperator C μ (Y t)
      (Jacobian.controlInput (acc t) (ω t))))
    (hc : Continuous (fun t => coefficient μ r D p α w (Y t).pos))
    (hΨ : ∀ t, HasDerivAt (fun s => (Ψ s).val) (B t*(Ψ t).val) t)
    (hdefect : ∀ t ∈ Icc 0 T,
      ‖scaledOperator C μ (Y t) (Jacobian.controlInput (acc t) (ω t))-B t‖≤e t)
    (hegain : ∀ t ∈ Icc 0 T,
      (∫ s in 0..t, ‖NearLinearTube.kernel Ψ t s‖*e s)≤d)
    (hΨ₀ : Ψ 0=1)
    (hinitial : C.symm (coordinates φ (X 0) (Y 0)) ∈ initial)
    (hi : ‖C.symm (coordinates φ (X 0) (Y 0))‖≤a)
    (hlin : ∀ t ∈ Icc 0 T,
      ‖(Ψ t).val (C.symm (coordinates φ (X 0) (Y 0)))‖≤a)
    (hgain : ∀ t ∈ Icc 0 T,
      (∫ s in 0..t, ‖NearLinearTube.kernel Ψ t s‖*
        coefficient μ r D p α w (Y s).pos)≤b) :
    ∀ t ∈ Icc 0 T,
      ‖C.symm (coordinates φ (X t) (Y t))‖≤LinearQuadraticTube.radius a d b ∧
      ‖C.symm (coordinates φ (X t) (Y t))-
        (Ψ t).val (C.symm (coordinates φ (X 0) (Y 0)))‖≤
          d*LinearQuadraticTube.radius a d b+b*(LinearQuadraticTube.radius a d b)^2 ∧
      enorm (coordinates φ (X t) (Y t) 2)=enorm φ ∧
      enorm ((X t).pos-(Y t).pos)≤D ∧
      r-D≤enorm (X t).pos ∧
      X t ∈ reachableTube C Ψ (Y t) initial
        (d*LinearQuadraticTube.radius a d b+b*(LinearQuadraticTube.radius a d b)^2) t := by
  obtain ⟨x, dx, hx, hdx, hderiv, hexp, hangle, hcoords⟩ :=
    exists_lift X Y acc ω gx gy hacc hω hgx hgy hX hY φ hφ hrot
  have result := OrbitalApproximateTube.certificate C μ hμ X Y x dx
    (fun t => Jacobian.controlInput (acc t) (ω t)) Ψ B e
    hT ha hd0 hd1 hb hsmall hp hα hw hD hposDomain hangDomain
    hscalep hscaleα hscalew hq hx hdx (fun t _ => hderiv t)
    (fun t ht => by
      rw [← hgX t ht]
      exact (spacecraft_ode_iff X (acc t) (ω t) (gx t) t).mp (hX t))
    (fun t ht => by
      rw [← hgY t ht]
      exact (spacecraft_ode_iff Y (acc t) (ω t) (gy t) t).mp (hY t))
    hexp hB hec he0 hA hc hΨ hdefect hegain hΨ₀
    (by simpa only [hcoords] using hi)
    (fun t ht => by simpa only [hcoords] using hlin t ht) hgain
  intro t ht
  obtain ⟨htotal, herr, _, hpos⟩ := result t ht
  have hmem := mem_reachableTube C Ψ (X t) (Y t) (x t) (C.symm (x 0))
    initial (hexp t) (by simpa only [hcoords] using hinitial) herr
  have hnorm : enorm (Y t).pos ≤ enorm ((X t).pos-(Y t).pos)+enorm (X t).pos := by
    have heq : (Y t).pos = -((X t).pos-(Y t).pos)+(X t).pos := by abel
    calc
      _ = enorm (-((X t).pos-(Y t).pos)+(X t).pos) := congrArg enorm heq
      _ ≤ _ := by simpa only [enorm_neg] using enorm_add_le (-((X t).pos-(Y t).pos)) (X t).pos
  refine ⟨?_, ?_, ?_, hpos, ?_, hmem⟩
  · simpa only [hcoords] using htotal
  · simpa only [hcoords] using herr
  · simpa only [hcoords] using hangle t
  · linarith [hq t ht]

end GNC.SharedInputOrbitalTube
