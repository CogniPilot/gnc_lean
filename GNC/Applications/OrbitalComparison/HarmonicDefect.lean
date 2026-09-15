import GNC.Applications.OrbitalComparison.HarmonicFrame

/-! Complete physical defect for the prescribed harmonic pointing family.
The phase is retained exactly; the amplitude truncation and the actual
inverse-square gravity remainder are both charged. -/
namespace GNC.OrbitalComparison.HarmonicDefect
open HarmonicPolynomial (Coeff Operator harmonic linear)
open HarmonicBurn (amplitude phase pointing)
open UniformCertificate

def thrustScale : ℚ := 360000*Direct.thrust
def firstSource : Coeff :=
  ![![0,0],![0,(4/5)*thrustScale*amplitude],![0,(3/5)*thrustScale*amplitude]]
def secondSource : Coeff := ![![thrustScale*amplitude^2/4,0],![0,0],![0,0]]
def meanSource : Coeff := -secondSource
def sourceBudget : ℚ := thrustScale*(amplitude^3/6+amplitude^4/24)

noncomputable section
open SpatialBurn SpatialRotatingFrame SpatialExactNominal HarmonicFrame Real Set

def sineDirection : E3 := pack 0 (4/5) (3/5)
def cosineDirection : E3 := pack (-1) 0 0

theorem direction_norms : ‖sineDirection‖ = 1 ∧ ‖cosineDirection‖ = 1 := by
  have hs := pack_norm_sq 0 (4/5) (3/5)
  have hc := pack_norm_sq (-1) 0 0
  dsimp [sineDirection,cosineDirection]
  constructor <;> nlinarith [norm_nonneg (pack 0 (4/5) (3/5)),norm_nonneg (pack (-1) 0 0)]

def approximate (ψ : ℝ) : E3 := harmonic meanSource 0+
  harmonic firstSource ψ+harmonic secondSource (2*ψ)

theorem approximate_identity (ψ : ℝ) : approximate ψ =
    (thrustScale:ℝ) • HarmonicPointing.source (amplitude:ℝ) ψ sineDirection cosineDirection := by
  ext i
  fin_cases i <;>
    simp [approximate,meanSource,firstSource,secondSource,HarmonicPolynomial.harmonic,
      HarmonicPolynomial.column,HarmonicPointing.source,sineDirection,cosineDirection,pack_eq] <;> ring

theorem thrustScale_nonneg : (0:ℚ) ≤ thrustScale := by
  have h : (0:ℚ) ≤ Direct.thrust := by
    exact_mod_cast SpatialFieldCertificate.physical_constants.2.2
  exact mul_nonneg (by norm_num) h

theorem sourceBudget_nonneg : (0:ℚ) ≤ sourceBudget := by
  have h := thrustScale_nonneg
  dsimp [sourceBudget,amplitude]
  positivity

theorem input_as_rotated (ω φ t : ℝ) : HarmonicBurn.input ω φ t =
    turn t ((thrustScale:ℝ) • FiniteAngleComparison.exactAngle (pointing ω φ t)
      sineDirection cosineDirection) := by
  rw [HarmonicBurn.input,HarmonicBurn.source,rtn_source,rtn_source]
  ext i
  fin_cases i <;>
    simp [turn,mix,pack_eq,FiniteAngleComparison.exactAngle,sineDirection,cosineDirection,
      thrustScale] <;> ring

theorem source_error (ω φ t : ℝ) :
    ‖HarmonicBurn.input ω φ t-turn t (approximate (phase ω φ t))‖ ≤ (sourceBudget:ℝ) := by
  rw [input_as_rotated,← map_sub,turn_norm,approximate_identity,← smul_sub,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (by exact_mod_cast thrustScale_nonneg)]
  have h := HarmonicPointing.source_bound (amplitude:ℝ) (phase ω φ t)
    (by norm_num [amplitude]) sineDirection cosineDirection
  rw [direction_norms.1,direction_norms.2,mul_one,mul_one] at h
  have hf : (0:ℝ) ≤ thrustScale := by exact_mod_cast thrustScale_nonneg
  simpa [sourceBudget,pointing] using mul_le_mul_of_nonneg_left h hf

def linearDefect (d v a : E3) (ψ : ℝ) : E3 :=
  a-linear positionOperator d-linear velocityOperator v-approximate ψ

theorem physical_defect_identity (ω φ t : ℝ) (d v a : ℝ → E3) :
    HarmonicFrame.acceleration d v a t-
      HarmonicBurn.acceleration ω φ t (position d t) =
    turn t (linearDefect (d t) (v t) (a t) (phase ω φ t))-
      (360000:ℝ) • (Gravity.field mu (nominal.p t+turn t (d t))-
        Gravity.field mu (nominal.p t)-Gravity.gradient mu (nominal.p t) (turn t (d t)))+
      (turn t (approximate (phase ω φ t))-HarmonicBurn.input ω φ t) := by
  rw [linearDefect,← linear_residual_identity]
  dsimp [HarmonicFrame.acceleration,HarmonicBurn.acceleration,position,
    SpatialFieldCertificate.physicalAcceleration,HarmonicBurn.input]
  module

/-- The radius in this bound is the candidate displacement, not an assumed
unknown-trajectory tube. The separate first-exit check closes that tube. -/
theorem physical_defect_bound (ω φ t : ℝ) (d v a : ℝ → E3) {s D : ℝ}
    (hd : ‖d t‖ ≤ s) (hs : s < 7000000)
    (hD : ‖linearDefect (d t) (v t) (a t) (phase ω φ t)‖ ≤ D) :
    ‖HarmonicBurn.acceleration ω φ t (position d t)-HarmonicFrame.acceleration d v a t‖ ≤
      D+(sourceBudget:ℝ)+360000*Gravity.remainderBound mu 7000000 s := by
  have hg := Gravity.remainder_bound_of_norm_le mu (by norm_num [mu]) (nominal.p t)
    (turn t (d t)) (by simpa only [turn_norm] using hd) (by simpa only [nominal_norm] using hs)
  rw [nominal_norm] at hg
  have hscaled : ‖(360000:ℝ) • (Gravity.field mu (nominal.p t+turn t (d t))-
      Gravity.field mu (nominal.p t)-Gravity.gradient mu (nominal.p t) (turn t (d t)))‖ ≤
      360000*Gravity.remainderBound mu 7000000 s := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<360000)] using
      mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 360000)
  rw [norm_sub_rev,physical_defect_identity]
  have hsour : ‖turn t (approximate (phase ω φ t))-HarmonicBurn.input ω φ t‖ ≤ (sourceBudget:ℝ) := by
    rw [norm_sub_rev]
    exact source_error ω φ t
  have htriangle := norm_sub_le
    (turn t (linearDefect (d t) (v t) (a t) (phase ω φ t)))
    ((360000:ℝ) • (Gravity.field mu (nominal.p t+turn t (d t))-
      Gravity.field mu (nominal.p t)-Gravity.gradient mu (nominal.p t) (turn t (d t))))
  rw [turn_norm] at htriangle
  exact (norm_add_le _ _).trans (by linarith)

end
end GNC.OrbitalComparison.HarmonicDefect
