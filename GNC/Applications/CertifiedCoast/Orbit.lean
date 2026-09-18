import GNC.Applications.CertifiedCoast.Data.CoastStep00
import GNC.Applications.CertifiedCoast.Data.CoastStep01
import GNC.Applications.CertifiedCoast.Data.CoastStep02
import GNC.Applications.CertifiedCoast.Data.CoastStep03
import GNC.Applications.CertifiedCoast.Data.CoastStep04
import GNC.Applications.CertifiedCoast.Data.CoastStep05
import GNC.Applications.CertifiedCoast.Data.CoastStep06
import GNC.Applications.CertifiedCoast.Data.CoastStep07
import GNC.Applications.CertifiedCoast.Data.CoastStep08
import GNC.Applications.CertifiedCoast.Data.CoastStep09
import GNC.Applications.CertifiedCoast.Data.CoastStep10
import GNC.Applications.CertifiedCoast.Data.CoastStep11
import GNC.Applications.CertifiedCoast.Data.CoastStep12
import GNC.Applications.CertifiedCoast.Data.CoastStep13
import GNC.Applications.CertifiedCoast.Data.CoastStep14
import GNC.Applications.CertifiedCoast.Data.CoastStep15
import GNC.Applications.CertifiedCoast.Data.CoastStep16
import GNC.Applications.CertifiedCoast.Data.CoastStep17
import GNC.Applications.CertifiedCoast.Data.CoastStep18
import GNC.Applications.CertifiedCoast.Data.CoastStep19
import GNC.Applications.CertifiedCoast.Data.CoastStep20
import GNC.Applications.CertifiedCoast.Data.CoastStep21
import GNC.Applications.CertifiedCoast.Data.CoastStep22
import GNC.Applications.CertifiedCoast.Data.CoastStep23
import GNC.Applications.CertifiedCoast.Data.CoastStep24
import GNC.Applications.CertifiedCoast.Data.CoastStep25
import GNC.Applications.CertifiedCoast.Data.CoastStep26
import GNC.Applications.CertifiedCoast.Data.CoastStep27
import GNC.Applications.CertifiedCoast.Data.CoastStep28
import GNC.Applications.CertifiedCoast.Data.CoastStep29
import GNC.Applications.CertifiedCoast.Data.CoastStep30
import GNC.Applications.CertifiedCoast.Data.CoastStep31
import GNC.Applications.CertifiedCoast.Chain

/-! Whole-orbit certified coast: 32 steps of a degree-20 Taylor
integrator over one Kepler period. Each step's rational certificate is checked
by the kernel; the chain composes them into a terminal error bound for every
true inverse-square solution seeded within the initial radii. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace GNC.CertifiedCoast.Orbit
open GNC.CertifiedCoast GNC.PlanarCoast GNC.PlanarCoast.Candidate Set
def steps : ℕ → Step
  | 0 => Data.CoastStep00.data
  | 1 => Data.CoastStep01.data
  | 2 => Data.CoastStep02.data
  | 3 => Data.CoastStep03.data
  | 4 => Data.CoastStep04.data
  | 5 => Data.CoastStep05.data
  | 6 => Data.CoastStep06.data
  | 7 => Data.CoastStep07.data
  | 8 => Data.CoastStep08.data
  | 9 => Data.CoastStep09.data
  | 10 => Data.CoastStep10.data
  | 11 => Data.CoastStep11.data
  | 12 => Data.CoastStep12.data
  | 13 => Data.CoastStep13.data
  | 14 => Data.CoastStep14.data
  | 15 => Data.CoastStep15.data
  | 16 => Data.CoastStep16.data
  | 17 => Data.CoastStep17.data
  | 18 => Data.CoastStep18.data
  | 19 => Data.CoastStep19.data
  | 20 => Data.CoastStep20.data
  | 21 => Data.CoastStep21.data
  | 22 => Data.CoastStep22.data
  | 23 => Data.CoastStep23.data
  | 24 => Data.CoastStep24.data
  | 25 => Data.CoastStep25.data
  | 26 => Data.CoastStep26.data
  | 27 => Data.CoastStep27.data
  | 28 => Data.CoastStep28.data
  | 29 => Data.CoastStep29.data
  | 30 => Data.CoastStep30.data
  | _ => Data.CoastStep31.data

theorem valid (j : ℕ) (hj : j < 32) : (steps j).Valid := by
  interval_cases j
  · exact Data.CoastStep00.valid
  · exact Data.CoastStep01.valid
  · exact Data.CoastStep02.valid
  · exact Data.CoastStep03.valid
  · exact Data.CoastStep04.valid
  · exact Data.CoastStep05.valid
  · exact Data.CoastStep06.valid
  · exact Data.CoastStep07.valid
  · exact Data.CoastStep08.valid
  · exact Data.CoastStep09.valid
  · exact Data.CoastStep10.valid
  · exact Data.CoastStep11.valid
  · exact Data.CoastStep12.valid
  · exact Data.CoastStep13.valid
  · exact Data.CoastStep14.valid
  · exact Data.CoastStep15.valid
  · exact Data.CoastStep16.valid
  · exact Data.CoastStep17.valid
  · exact Data.CoastStep18.valid
  · exact Data.CoastStep19.valid
  · exact Data.CoastStep20.valid
  · exact Data.CoastStep21.valid
  · exact Data.CoastStep22.valid
  · exact Data.CoastStep23.valid
  · exact Data.CoastStep24.valid
  · exact Data.CoastStep25.valid
  · exact Data.CoastStep26.valid
  · exact Data.CoastStep27.valid
  · exact Data.CoastStep28.valid
  · exact Data.CoastStep29.valid
  · exact Data.CoastStep30.valid
  · exact Data.CoastStep31.valid

theorem joins (j : ℕ) (hj : j+1 < 32) : (steps j).Compatible (steps (j+1)) := by
  have hj' : j ≤ 30 := by omega
  interval_cases j <;> decide +kernel

/-- Terminal certified position error radius (normalized length). -/
def rpEndFinal : ℚ := (1433319467062110043/633825300114114700748351602688)
/-- Terminal certified velocity error radius (normalized velocity). -/
def rvEndFinal : ℚ := (1012256469338923095/316912650057057350374175801344)

theorem terminal (w : ℕ → ℝ → Fin 4 → ℝ)
    (hwc : ∀ j < 32, Continuous (w j))
    (hw : ∀ j < 32, ∀ t ∈ Icc (0:ℝ) ((steps j).c.h:ℝ),
      HasDerivAt (w j) (PolynomialOrbit.physicalRate 0 (w j t)) t)
    (hjoin : ∀ j, j+1 < 32 → w (j+1) 0 = w j ((steps j).c.h:ℝ))
    (hp0 : ‖truePos (w 0) 0-(steps 0).c.pos 0‖ ≤ ((steps 0).rp:ℝ))
    (hv0 : ‖trueVel (w 0) 0-(steps 0).c.dpos 0‖ ≤ ((steps 0).rv:ℝ)) :
    ‖truePos (w 31) ((steps 31).c.h:ℝ)-(steps 31).c.pos ((steps 31).c.h:ℝ)‖ ≤ (rpEndFinal:ℝ) ∧
      ‖trueVel (w 31) ((steps 31).c.h:ℝ)-(steps 31).c.dpos ((steps 31).c.h:ℝ)‖ ≤ (rvEndFinal:ℝ) := by
  have hterm := chain_terminal steps 31 valid joins w hwc hw hjoin hp0 hv0
  have hp : (steps 31).rpEnd = rpEndFinal := by rfl
  have hv : (steps 31).rvEnd = rvEndFinal := by rfl
  rw [hp, hv] at hterm
  exact hterm

/-- Initial radii of the chain (normalized). -/
theorem initial_radii : (steps 0).rp = 0 ∧ (steps 0).rv = (1/22517998136852480) :=
  ⟨by rfl, by rfl⟩

/-- Terminal SI error bounds: position in metres, velocity in metres/second. -/
def positionBoundSI : ℚ := (156769316709918285953125/9903520314283042199192993792)
def velocityBoundSI : ℚ := (1909723055054812311027/79228162514264337593543950336)

theorem terminal_SI (w : ℕ → ℝ → Fin 4 → ℝ)
    (hwc : ∀ j < 32, Continuous (w j))
    (hw : ∀ j < 32, ∀ t ∈ Icc (0:ℝ) ((steps j).c.h:ℝ),
      HasDerivAt (w j) (PolynomialOrbit.physicalRate 0 (w j t)) t)
    (hjoin : ∀ j, j+1 < 32 → w (j+1) 0 = w j ((steps j).c.h:ℝ))
    (hp0 : ‖truePos (w 0) 0-(steps 0).c.pos 0‖ ≤ ((steps 0).rp:ℝ))
    (hv0 : ‖trueVel (w 0) 0-(steps 0).c.dpos 0‖ ≤ ((steps 0).rv:ℝ)) :
    (radiusSI:ℝ)*‖truePos (w 31) ((steps 31).c.h:ℝ)-(steps 31).c.pos ((steps 31).c.h:ℝ)‖ ≤ (positionBoundSI:ℝ) ∧
      (speedSI:ℝ)*‖trueVel (w 31) ((steps 31).c.h:ℝ)-(steps 31).c.dpos ((steps 31).c.h:ℝ)‖ ≤ (velocityBoundSI:ℝ) := by
  have hsi := physical_bounds_SI steps 31 valid joins w hwc hw hjoin hp0 hv0
  have hp : (radiusSI:ℝ)*((steps 31).rpEnd:ℝ) = (positionBoundSI:ℝ) := by
    norm_num [radiusSI, positionBoundSI, show (steps 31).rpEnd = rpEndFinal from rfl, rpEndFinal]
  have hv : (speedSI:ℝ)*((steps 31).rvEnd:ℝ) = (velocityBoundSI:ℝ) := by
    norm_num [speedSI, velocityBoundSI, show (steps 31).rvEnd = rvEndFinal from rfl, rvEndFinal]
  exact ⟨hsi.1.trans_eq hp, hsi.2.trans_eq hv⟩

end GNC.CertifiedCoast.Orbit
