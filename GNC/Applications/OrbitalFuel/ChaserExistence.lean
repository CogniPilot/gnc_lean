import GNC.Applications.OrbitalFuel.ChaserReferenceData
import GNC.Applications.OrbitalFuel.TerminalResponse

/-! Existence of the actual three-dimensional switched nonlinear chaser,
with the paper's initial conditions and all eighteen physical burn vectors.
The whole-horizon noncollision conclusion follows from an inactive extension.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ChaserExistence
open GNC PolynomialOrbit PolynomialOrbitTransition Set ChaserReferenceData

def initial : ChaserExtension.State :=
  (![0,-10000000/(FreeResponse.lengthUnit:ℝ),1000000/(FreeResponse.lengthUnit:ℝ)],
    ![(5/16)*Real.sqrt (3/2)*(10000000/(FreeResponse.lengthUnit:ℝ)),0,0])

theorem initial_bound : ‖initial‖ ≤ (1/10000:ℝ) := by
  have hs : Real.sqrt (3/2:ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/2),Real.sqrt_nonneg (3/2:ℝ)]
  have hs0 := Real.sqrt_nonneg (3/2:ℝ)
  unfold initial
  generalize Real.sqrt (3/2:ℝ) = s at *
  apply norm_prod_le_iff.mpr
  constructor
  all_goals
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/10000)).mpr
    intro i
    fin_cases i <;> norm_num [FreeResponse.lengthUnit,Real.norm_eq_abs,abs_of_nonneg hs0]
    all_goals nlinarith

structure Motion (r : Flow) (commands : Fin 18 → Vec3) where
  p : ℝ → Vec3
  v : ℝ → Vec3
  hp : Continuous p
  hv : Continuous v
  noncollision : ∀ t ∈ Icc (0:ℝ) (3/5), p t ≠ 0
  initialPlane : PlanarChaserError.plane (r.w 0) (p 0) (v 0) =
    TerminalResponse.initialPlane (Real.sqrt (3/2))
  initialNormal : PlanarChaserError.normal (p 0) (v 0) = TerminalResponse.initialNormal
  position_derivative : ∀ k < 37,
    ∀ t ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ), HasDerivAt p (v t) t
  velocity_derivative : ∀ k < 37,
    ∀ t ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt v (Gravity.field3 1 (p t)+acceleration r commands k t) t

theorem exists_motion (r : Flow) (commands : Fin 18 → Vec3)
    (hcommands : ∀ j, GNC.enorm (commands j) ≤ 1) : Nonempty (Motion r commands) := by
  obtain ⟨x,hx,hi,hb,hd⟩ := ChaserContinuation.exists_relative (center r) (thrust r)
    (center_continuous r) (thrust_continuous r) (center_lower r) (thrust_bound r)
    (acceleration r commands) nodes 37 (fun k _ => acceleration_continuous r commands k)
    (fun k _ t _ => acceleration_bound r commands hcommands k t)
    nodes_monotone nodes_zero nodes_final initial initial_bound
  let p : ℝ → Vec3 := fun t => position (r.w t)+(x t).1
  let v : ℝ → Vec3 := fun t => velocity (r.w t)+(4:ℝ) • (x t).2
  have hw := r.hw
  have hpref : Continuous (fun t => position (r.w t)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [position,Matrix.cons_val_two] <;> fun_prop
  have hvref : Continuous (fun t => velocity (r.w t)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [velocity,Matrix.cons_val_two] <;> fun_prop
  have hp : Continuous p := hpref.add hx.fst
  have hv : Continuous v := hvref.add (hx.snd.const_smul (4:ℝ))
  have hc (t : ℝ) (ht : t ∈ Icc (0:ℝ) (3/5)) : center r t = position (r.w t) := by
    simp only [ChaserReferenceData.center,clamp_eq ht]
  have ha (t : ℝ) (ht : t ∈ Icc (0:ℝ) (3/5)) :
      thrust r t = PlanarChaserError.referenceThrust (PolynomialTransition.alpha:ℝ) (r.w t) := by
    simp only [thrust,clamp_eq ht]
  have htfull (k : ℕ) (hk : k < 37) (t : ℝ)
      (ht : t ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ)) :
      t ∈ Icc (0:ℝ) (3/5) :=
    ⟨(BurnSchedule.horizon k hk).1.trans ht.1.le,ht.2.le.trans (BurnSchedule.horizon k hk).2⟩
  have hdarc (k : ℕ) (hk : k < 37) (t : ℝ)
      (ht : t ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ)) :=
    hd k hk t (by simpa only [nodes_eq k (by omega),nodes_eq (k+1) (by omega)] using ht)
  refine ⟨⟨p,v,hp,hv,?_,?_,?_,?_,?_⟩⟩
  · intro t ht
    have hrad := center_lower r t
    rw [hc t ht] at hrad
    have hpbound : ‖(x t).1‖ ≤ (1/20:ℝ) := by
      have h := norm_fst_le (x t)
      linarith [hb t ht]
    have h := ChaserExtension.shift_radius _ _ hrad hpbound
    intro hz
    have he : GNC.enorm (p t) = 0 := (GNC.enorm_eq_zero_iff _).mpr hz
    change (69/100:ℝ) ≤ GNC.enorm (p t) at h
    linarith
  · ext i
    fin_cases i <;>
      simp [PlanarChaserError.plane,p,v,hi,initial,position,velocity,TerminalResponse.initialPlane]
    all_goals ring
  · ext i
    fin_cases i <;>
      simp [PlanarChaserError.normal,p,v,hi,initial,position,velocity,TerminalResponse.initialNormal]
  · intro k hk t ht
    have h := (Reference.position_derivative (r.hdw t (htfull k hk t ht))).fun_add
      (hdarc k hk t ht).fst
    simpa only [p,v,ChaserContinuation.rate] using h
  · intro k hk t ht
    have href := Reference.velocity_derivative (r.hdw t (htfull k hk t ht))
    rw [← Reference.thrust_tangent] at href
    have hdx : HasDerivAt (fun s => (x s).2)
        (ChaserContinuation.rate (ChaserReferenceData.center r t) (thrust r t)
          (acceleration r commands k t) (x t)).2 t := (hdarc k hk t ht).snd
    have h := href.fun_add (hdx.const_smul (4:ℝ))
    have he : Gravity.field3 1 (position (r.w t))+
        PlanarChaserError.referenceThrust (PolynomialTransition.alpha:ℝ) (r.w t)+
        (4:ℝ) • (ChaserContinuation.rate (center r t) (thrust r t)
          (acceleration r commands k t) (x t)).2 =
        Gravity.field3 1 (p t)+acceleration r commands k t := by
      rw [ChaserContinuation.rate,hc t (htfull k hk t ht),ha t (htfull k hk t ht)]
      simp only [smul_smul,show (4:ℝ)*(1/4) = 1 by norm_num,one_smul]
      dsimp [p]
      abel
    rw [he] at h
    exact h

end GNC.Applications.OrbitalFuel.ChaserExistence
