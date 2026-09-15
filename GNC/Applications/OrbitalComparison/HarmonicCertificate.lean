import GNC.Applications.OrbitalComparison.HarmonicMode
import GNC.Dynamics.PolynomialOrbitCertificate

/-! A complete certificate interface for a prescribed pointing oscillation.
Every phase is covered. Both the Sylvester solver and the classical
inverse-frequency construction can submit the same exact-rational data. -/
namespace GNC.OrbitalComparison.HarmonicCertificate
open HarmonicMode HarmonicDefect
open HarmonicPolynomial (Coeff harmonic linear)
open HarmonicFrame (positionOperator velocityOperator)

def positionGain (k : ℚ) : ℚ := 1/2+k/24+k^2/720+k^3/(720*(56-k))
def velocityGain (k : ℚ) : ℚ := 1+k/6+k^2/120+k^3/(90*(56-k))

structure Data where
  /-- Angular frequency with respect to normalized time `t/600`. -/
  frequency : ℚ
  mean : Mode
  first : Mode
  second : Mode

def Data.displacementBound (D : Data) : ℚ :=
  D.mean.positionBound+D.first.positionBound+D.second.positionBound
def Data.rateBound (D : Data) : ℚ :=
  D.mean.velocityBound+D.first.velocityBound+D.second.velocityBound
def Data.linearBudget (D : Data) : ℚ :=
  D.mean.residualBound+D.first.residualBound+D.second.residualBound
def Data.gravityBudget (D : Data) : ℚ :=
  360000*Direct.gravityParameter*D.displacementBound^2*(3*7000000-2*D.displacementBound)/
    (7000000^3*(7000000-D.displacementBound)^2)
def Data.defect (D : Data) : ℚ := D.linearBudget+sourceBudget+D.gravityBudget
def Data.gain (D : Data) : ℚ :=
  360000*2*Direct.gravityParameter/(7000000-2*D.displacementBound)^3
def Data.positionError (D : Data) : ℚ := D.defect*positionGain D.gain
def Data.velocityError (D : Data) : ℚ := D.defect*velocityGain D.gain/600
def Data.physicalVelocityBound (D : Data) : ℚ :=
  (D.rateBound+UniformCertificate.omega*D.displacementBound)/600+D.velocityError

def Data.Valid (D : Data) : Prop :=
  D.mean.Valid 0 meanSource 0 ∧ D.first.Valid D.frequency 0 firstSource ∧
  D.second.Valid (2*D.frequency) 0 secondSource ∧
  0 < D.displacementBound ∧ D.displacementBound < 3500000 ∧
  0 ≤ D.gain ∧ D.gain < 56 ∧ 0 ≤ D.defect ∧ D.positionError < D.displacementBound

instance (D : Data) : Decidable D.Valid := by unfold Data.Valid; infer_instance

noncomputable section
open SpatialBurn SpatialExactNominal HarmonicFrame Set

theorem positionGain_cast (k : ℚ) : (positionGain k:ℝ) = PolynomialSupersolution.value (k:ℝ) 1 := by
  simp [positionGain,PolynomialSupersolution.value,PolynomialSupersolution.polynomial]

theorem velocityGain_cast (k : ℚ) : (velocityGain k:ℝ) = PolynomialSupersolution.velocity (k:ℝ) 1 := by
  simp [velocityGain,PolynomialSupersolution.velocity,PolynomialSupersolution.polynomial,
    Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow,
    div_eq_mul_inv,mul_inv_rev]
  ring

def Data.displacement (D : Data) (φ t : ℝ) : E3 :=
  D.mean.position 0 0 t+D.first.position D.frequency φ t+D.second.position (2*D.frequency) (2*φ) t
def Data.rotatingVelocity (D : Data) (φ t : ℝ) : E3 :=
  D.mean.velocity 0 0 t+D.first.velocity D.frequency φ t+D.second.velocity (2*D.frequency) (2*φ) t
def Data.rotatingAcceleration (D : Data) (φ t : ℝ) : E3 :=
  D.mean.acceleration 0 0 t+D.first.acceleration D.frequency φ t+
    D.second.acceleration (2*D.frequency) (2*φ) t

theorem Data.derivative_displacement (D : Data) (φ t : ℝ) :
    HasDerivAt (D.displacement φ) (D.rotatingVelocity φ t) t :=
  ((D.mean.derivative_position 0 0 t).add (D.first.derivative_position D.frequency φ t)).add
    (D.second.derivative_position (2*D.frequency) (2*φ) t)

theorem Data.derivative_rotatingVelocity (D : Data) (φ t : ℝ) :
    HasDerivAt (D.rotatingVelocity φ) (D.rotatingAcceleration φ t) t :=
  ((D.mean.derivative_velocity 0 0 t).add (D.first.derivative_velocity D.frequency φ t)).add
    (D.second.derivative_velocity (2*D.frequency) (2*φ) t)

theorem Data.initial (D : Data) (h : D.Valid) (φ : ℝ) :
    D.displacement φ 0 = 0 ∧ D.rotatingVelocity φ 0 = 0 := by
  have h0 := D.mean.initial 0 meanSource 0 h.1 0
  have h1 := D.first.initial D.frequency 0 firstSource h.2.1 φ
  have h2 := D.second.initial (2*D.frequency) 0 secondSource h.2.2.1 (2*φ)
  simp only [Data.displacement,Data.rotatingVelocity,h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,add_zero,and_self]

private theorem three_bounds {x y z : E3} {a b c : ℝ}
    (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) (hz : ‖z‖ ≤ c) : ‖x+y+z‖ ≤ a+b+c :=
  (norm_add_le (x+y) z).trans
    (add_le_add ((norm_add_le x y).trans (add_le_add hx hy)) hz)

theorem Data.displacement_bound (D : Data) (h : D.Valid) (φ : ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    ‖D.displacement φ t‖ ≤ (D.displacementBound:ℝ) := by
  simpa only [Data.displacement,Data.displacementBound,Rat.cast_add] using three_bounds
    (D.mean.position_bound 0 meanSource 0 h.1 0 ht)
    (D.first.position_bound D.frequency 0 firstSource h.2.1 φ ht)
    (D.second.position_bound (2*D.frequency) 0 secondSource h.2.2.1 (2*φ) ht)

theorem Data.rotatingVelocity_bound (D : Data) (h : D.Valid) (φ : ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    ‖D.rotatingVelocity φ t‖ ≤ (D.rateBound:ℝ) := by
  simpa only [Data.rotatingVelocity,Data.rateBound,Rat.cast_add] using three_bounds
    (D.mean.velocity_bound 0 meanSource 0 h.1 0 ht)
    (D.first.velocity_bound D.frequency 0 firstSource h.2.1 φ ht)
    (D.second.velocity_bound (2*D.frequency) 0 secondSource h.2.2.1 (2*φ) ht)

theorem Data.linear_defect_bound (D : Data) (h : D.Valid) (φ : ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    ‖linearDefect (D.displacement φ t) (D.rotatingVelocity φ t) (D.rotatingAcceleration φ t)
      (HarmonicBurn.phase (D.frequency:ℝ) φ t)‖ ≤ (D.linearBudget:ℝ) := by
  have h0 := D.mean.residual_bound 0 meanSource 0 h.1 0 ht
  have h1 := D.first.residual_bound D.frequency 0 firstSource h.2.1 φ ht
  have h2 := D.second.residual_bound (2*D.frequency) 0 secondSource h.2.2.1 (2*φ) ht
  have htri := three_bounds h0 h1 h2
  have he : ((2*D.frequency:ℚ):ℝ)*t+2*φ = 2*((D.frequency:ℝ)*t+φ) := by push_cast; ring
  rw [he] at htri
  convert htri using 1
  · congr 1
    simp only [linearDefect,Data.displacement,Data.rotatingVelocity,Data.rotatingAcceleration,
      approximate,HarmonicBurn.phase,map_add,HarmonicPolynomial.harmonic_zero,sub_zero]
    abel
  · simp only [Data.linearBudget,Rat.cast_add]

def Data.position (D : Data) (φ : ℝ) : ℝ → E3 := HarmonicFrame.position (D.displacement φ)
def Data.velocity (D : Data) (φ : ℝ) : ℝ → E3 :=
  HarmonicFrame.velocity (D.displacement φ) (D.rotatingVelocity φ)
def Data.acceleration (D : Data) (φ : ℝ) : ℝ → E3 :=
  HarmonicFrame.acceleration (D.displacement φ) (D.rotatingVelocity φ) (D.rotatingAcceleration φ)

theorem Data.derivative_position (D : Data) (φ : ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (D.position φ) (D.velocity φ t) t :=
  HarmonicFrame.position_derivative ht (D.derivative_displacement φ t)

theorem Data.derivative_velocity (D : Data) (φ : ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (D.velocity φ) (D.acceleration φ t) t :=
  HarmonicFrame.velocity_derivative ht (D.derivative_displacement φ t) (D.derivative_rotatingVelocity φ t)

theorem Data.continuous_position (D : Data) (φ : ℝ) : Continuous (D.position φ) :=
  nominal.continuous_p.add (continuous_iff_continuousAt.mpr fun t =>
    (turn_derivative (D.derivative_displacement φ t)).continuousAt)

theorem Data.continuous_velocity (D : Data) (φ : ℝ) : Continuous (D.velocity φ) :=
  nominal.continuous_v.add (continuous_iff_continuousAt.mpr fun t =>
    (turn_derivative ((D.derivative_rotatingVelocity φ t).add
      (spin_derivative (D.derivative_displacement φ t)))).continuousAt)

theorem Data.complete_defect_bound (D : Data) (h : D.Valid) (φ : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    ‖HarmonicBurn.acceleration (D.frequency:ℝ) φ t (D.position φ t)-D.acceleration φ t‖ ≤
      (D.defect:ℝ) := by
  have habs : |t| ≤ 1 := (abs_of_nonneg ht.1).symm ▸ ht.2
  have hs : (D.displacementBound:ℝ) < 3500000 := by exact_mod_cast h.2.2.2.2.1
  have hb := physical_defect_bound (D.frequency:ℝ) φ t
    (D.displacement φ) (D.rotatingVelocity φ) (D.rotatingAcceleration φ)
    (D.displacement_bound h φ habs) (by linarith) (D.linear_defect_bound h φ habs)
  convert hb using 1
  simp [Data.defect,Data.gravityBudget,Gravity.remainderBound,mu,Direct.gravityParameter]
  ring

theorem Data.radius_bound (D : Data) (h : D.Valid) (φ : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    7000000-2*(D.displacementBound:ℝ)+(D.displacementBound:ℝ) ≤ ‖D.position φ t‖ := by
  have habs : |t| ≤ 1 := (abs_of_nonneg ht.1).symm ▸ ht.2
  have hb := D.displacement_bound h φ habs
  have hn := norm_sub_le (D.position φ t) (turn t (D.displacement φ t))
  have he : D.position φ t-turn t (D.displacement φ t) = nominal.p t := by
    simp [Data.position,HarmonicFrame.position]
  rw [he,nominal_norm,turn_norm] at hn
  linarith

/-- A numerical record certifies every physical solution and every phase.
The region is proved by first exit; it is not supplied as a physical premise. -/
theorem Data.certifies (D : Data) (h : D.Valid) (φ : ℝ)
    (X : HarmonicBurn.Motion (D.frequency:ℝ) φ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-D.position φ t‖ ≤ (D.positionError:ℝ) ∧
      ‖X.v t-D.velocity φ t‖/600 ≤ (D.velocityError:ℝ) := by
  rcases h with ⟨h0,h1,h2,hs0,hs,hk0,hk,hF,hclose⟩
  have hsR : (D.displacementBound:ℝ) < 3500000 := by exact_mod_cast hs
  have hkR : (D.gain:ℝ) < 56 := by exact_mod_cast hk
  have hk0R : (0:ℝ) ≤ D.gain := by exact_mod_cast hk0
  have hFR : (0:ℝ) ≤ D.defect := by exact_mod_cast hF
  have hvalid : D.Valid := ⟨h0,h1,h2,hs0,hs,hk0,hk,hF,hclose⟩
  have hcR : (D.defect:ℝ)*PolynomialSupersolution.value (D.gain:ℝ) 1 < (D.displacementBound:ℝ) := by
    have hh : (D.positionError:ℝ) < (D.displacementBound:ℝ) := by exact_mod_cast hclose
    simpa only [Data.positionError,Rat.cast_mul,positionGain_cast] using hh
  have hi := D.initial hvalid φ
  have hbound := Gravity.constant_prediction mu 360000 (by norm_num [mu]) (by norm_num)
    X.p X.v (D.position φ) (D.velocity φ) (D.acceleration φ)
    (fun t => (Direct.thrust:ℝ) • HarmonicBurn.source (D.frequency:ℝ) φ t)
    hk0R hkR hFR (r := 7000000-2*(D.displacementBound:ℝ)) (by linarith) hcR
    (by simp [Data.gain,mu,Direct.gravityParameter]; ring_nf; exact le_rfl)
    (fun _ ht => D.radius_bound hvalid φ ht)
    X.continuous_p X.continuous_v (D.continuous_position φ) (D.continuous_velocity φ)
    X.derivative_p X.derivative_v (fun _ ht => D.derivative_position φ ht)
    (fun _ ht => D.derivative_velocity φ ht)
    (by simpa [Data.position,HarmonicFrame.position,hi.1] using X.initial_p)
    (by simpa [Data.velocity,HarmonicFrame.velocity,hi.1,hi.2] using X.initial_v)
    (fun _ ht => D.complete_defect_bound hvalid φ ht)
  intro t ht
  constructor
  · simpa only [Data.positionError,Rat.cast_mul,positionGain_cast] using (hbound t ht).1
  · have hv := div_le_div_of_nonneg_right (hbound t ht).2 (by norm_num : (0:ℝ) ≤ 600)
    simpa only [Data.velocityError,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,velocityGain_cast] using hv

theorem Data.physical_prediction (D : Data) (h : D.Valid) (φ : ℝ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖(HarmonicBurn.trajectory (D.frequency:ℝ) φ).p t-D.position φ t‖ ≤ (D.positionError:ℝ) ∧
      ‖(HarmonicBurn.trajectory (D.frequency:ℝ) φ).v t-D.velocity φ t‖/600 ≤ (D.velocityError:ℝ) :=
  D.certifies h φ (HarmonicBurn.trajectory (D.frequency:ℝ) φ)

theorem Data.physical_displacement (D : Data) (h : D.Valid) (φ : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(HarmonicBurn.trajectory (D.frequency:ℝ) φ).p t-nominal.p t‖ ≤
      ((D.displacementBound+D.positionError:ℚ):ℝ) := by
  have hp := (D.physical_prediction h φ t ht).1
  have hb := D.displacement_bound h φ ((abs_of_nonneg ht.1).symm ▸ ht.2)
  have he : (HarmonicBurn.trajectory (D.frequency:ℝ) φ).p t-nominal.p t =
      ((HarmonicBurn.trajectory (D.frequency:ℝ) φ).p t-D.position φ t)+
        turn t (D.displacement φ t) := by
    simp [Data.position,HarmonicFrame.position]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by rw [turn_norm,Rat.cast_add]; linarith)

theorem Data.physical_velocity (D : Data) (h : D.Valid) (φ : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(HarmonicBurn.trajectory (D.frequency:ℝ) φ).v t-nominal.v t‖/600 ≤
      (D.physicalVelocityBound:ℝ) := by
  have habs : |t| ≤ 1 := (abs_of_nonneg ht.1).symm ▸ ht.2
  have hv := (D.physical_prediction h φ t ht).2
  have hd := D.displacement_bound h φ habs
  have hrv := D.rotatingVelocity_bound h φ habs
  have hw : (0:ℝ) ≤ UniformCertificate.omega := by
    norm_num [UniformCertificate.omega,Direct.angularSpeed]
  have hs := (spin_bound (D.displacement φ t)).trans (mul_le_mul_of_nonneg_left hd hw)
  have hsum := (norm_add_le (D.rotatingVelocity φ t) (spin (D.displacement φ t))).trans
    (add_le_add hrv hs)
  have he : (HarmonicBurn.trajectory (D.frequency:ℝ) φ).v t-nominal.v t =
      ((HarmonicBurn.trajectory (D.frequency:ℝ) φ).v t-D.velocity φ t)+
        turn t (D.rotatingVelocity φ t+spin (D.displacement φ t)) := by
    simp [Data.velocity,HarmonicFrame.velocity]
    abel
  rw [he]
  have hn := norm_add_le
    ((HarmonicBurn.trajectory (D.frequency:ℝ) φ).v t-D.velocity φ t)
    (turn t (D.rotatingVelocity φ t+spin (D.displacement φ t)))
  rw [turn_norm] at hn
  simp only [Data.physicalVelocityBound,Rat.cast_add,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast]
  linarith

end
end GNC.OrbitalComparison.HarmonicCertificate
