import GNC.Analysis.DiskTimePolynomial
import GNC.Dynamics.PolynomialForcingCertificate
import GNC.Applications.OrbitalComparison.PointingCapDisk

/-! A complete cap certificate retaining the residual's time profile.
The same interface accepts direct, full-component and polynomial predictors.
It checks the physical inverse-square field, all cap points and every time. -/
namespace GNC.OrbitalComparison.PointingCapTimeCertificate
open PointingCapCertificate PointingCapPolynomial PointingCapBurn
open PointingCapRefinement PointingCapDisk SpatialBurn Set Planning.PolynomialKernel

structure Profile where
  residual : DiskTimePolynomial.Certificate 3
  envelope : List ℚ

def Profile.forcing (M : Profile) (D : Data) : List ℚ :=
  PolynomialBounds.add (M.residual.bound (depth D.sigma)) [D.sourceBudget+D.gravityBudget]

def Profile.positionError (M : Profile) : ℚ := evaluate M.envelope 1
def Profile.velocityError (M : Profile) (D : Data) : ℚ :=
  evaluate (differentiate M.envelope) 1/(600*D.alpha)

structure Profile.Valid (M : Profile) (D : Data) : Prop where
  residual : M.residual.Valid D.remainder D.sigma
  envelope : PolynomialForcing.Valid D.gain (M.forcing D) M.envelope
  region : evaluate (M.forcing D) 1*HarmonicCertificate.positionGain D.gain<D.positionBound

noncomputable section

theorem Profile.residual_bound (M : Profile) (D : Data) (hD : D.Valid) (hM : M.Valid D)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖vectorValue D.remainder x t‖≤PolynomialOrder.value (M.residual.bound (depth D.sigma)) t := by
  have hr := parameter_bounds (show (0:ℝ)≤D.sigma by exact_mod_cast hD.sigma_pos.le)
    (show (D.sigma:ℝ)^2<1 by exact_mod_cast D.valid_sigma hD) hx
  have hc : |x 2|≤(depth D.sigma:ℝ) := by simpa [depth] using hr.2.2
  simpa only [vector_value_eq] using M.residual.certifies D.remainder hM.residual hx.2.2.2 hc ht

theorem Profile.complete_defect (M : Profile) (D : Data) (hD : D.Valid) (hM : M.Valid D)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖PointingCapFrame.physicalAcceleration (D.alpha:ℝ) (direction x) t (D.position x t)-
      D.acceleration x t‖≤PolynomialOrder.value (M.forcing D) t := by
  have hb := coefficientBounds_sound D hD
  have hr : vectorValue D.rawResidual x t=vectorValue D.remainder x t := by
    ext i
    fin_cases i <;> simp [vectorValue,pack_eq,reduced_residual _ _ _ (hD.reduction _) hx t]
  have hL : ‖PointingCapDefect.residual (D.alpha:ℝ) (D.displacement x t)
      (D.rotatingVelocity x t) (D.rotatingAcceleration x t) (vectorValue D.first x t)
      (vectorValue D.source x t)‖≤PolynomialOrder.value (M.residual.bound (depth D.sigma)) t := by
    rw [← D.rawResidual_value,hr]
    exact M.residual_bound D hD hM hx ht
  have hP : (D.positionBound:ℝ)<7000000 :=
    (show (D.positionBound:ℝ)<3500000 by exact_mod_cast hD.position_max).trans (by norm_num)
  have h := PointingCapDefect.physical_defect_bound (D.alpha:ℝ) t (direction x)
    (D.displacement x) (D.rotatingVelocity x) (D.rotatingAcceleration x) (vectorValue D.first x)
    (vectorValue D.source x t) hP (hb.position x hx t ht) (hb.first x hx t ht)
    (hb.second x hx t ht) hL (D.source_bound hD hx t)
  convert h using 1
  rw [Profile.forcing,PolynomialOrder.value_add]
  simp [PolynomialOrder.value,evaluate,Data.gravityBudget,Data.timeScale,PointingCapFrame.scale,
    mu,Direct.gravityParameter,coefficientBounds]
  ring

/-- A profile bound and scalar supersolution give a complete physical error
bound. Initial conditions and existence come from the checked candidate. -/
theorem Profile.certifies_curve (M : Profile) (D : Data) (hD : D.Valid) (hM : M.Valid D)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x)
    (X : Motion (D.alpha:ℝ) (direction x)) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖X.p t-D.position x t‖≤PolynomialOrder.value M.envelope t ∧
      ‖X.v t-D.velocity x t‖/(600*(D.alpha:ℝ))≤
        PolynomialOrder.value (differentiate M.envelope) t/(600*(D.alpha:ℝ)) := by
  have hb := coefficientBounds_sound D hD
  have ha : (0:ℝ)<D.alpha := by exact_mod_cast hD.alpha_pos
  have hs : (D.positionBound:ℝ)<3500000 := by exact_mod_cast hD.position_max
  have hclose : PolynomialOrder.value (M.forcing D) 1*
      PolynomialSupersolution.value (D.gain:ℝ) 1<(D.positionBound:ℝ) := by
    have hh : ((evaluate (M.forcing D) 1:ℚ):ℝ)*
        (HarmonicCertificate.positionGain D.gain:ℝ)<(D.positionBound:ℝ) := by
      exact_mod_cast hM.region
    have hv := PolynomialOrder.value_at_rational (M.forcing D) 1
    simp only [Rat.cast_one] at hv
    simpa only [hv,HarmonicCertificate.positionGain_cast] using hh
  have hq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      7000000-2*(D.positionBound:ℝ)+(D.positionBound:ℝ)≤‖D.position x t‖ := by
    have hd := hb.position x hx t ht
    have hn := norm_sub_le (D.position x t) (PointingCapFrame.turn (D.alpha:ℝ) t (D.displacement x t))
    have he : D.position x t-PointingCapFrame.turn (D.alpha:ℝ) t (D.displacement x t)=
        PointingCapFrame.reference (D.alpha:ℝ) t := by simp [Data.position,PointingCapFrame.position]
    rw [he,PointingCapFrame.reference_norm,PointingCapFrame.turn_norm] at hn
    change ‖D.displacement x t‖≤(D.positionBound:ℝ) at hd
    linarith
  have hi := D.initial hD x
  have h := Gravity.polynomial_prediction_curve mu (PointingCapFrame.scale (D.alpha:ℝ))
    (by norm_num [mu]) (by unfold PointingCapFrame.scale; positivity)
    X.p X.v (D.position x) (D.velocity x) (D.acceleration x)
    (fun t => (Direct.thrust:ℝ) • PointingCapFrame.turn (D.alpha:ℝ) t (direction x))
    (M.forcing D) M.envelope hM.envelope hD.gain_nonnegative hD.gain_max
    (r := 7000000-2*(D.positionBound:ℝ)) (by linarith) hclose
    (by simp [Data.gain,Data.timeScale,PointingCapFrame.scale,mu,Direct.gravityParameter]; ring_nf; exact le_rfl)
    hq X.continuous_p X.continuous_v
    (continuous_iff_continuousAt.mpr fun t => (D.derivative_position x t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (D.derivative_velocity x t).continuousAt)
    X.derivative_p X.derivative_v (fun t _ => D.derivative_position x t)
    (fun t _ => D.derivative_velocity x t)
    (by simpa [Data.position,PointingCapFrame.position,hi.1] using X.initial_p)
    (by simpa [Data.velocity,PointingCapFrame.velocity,hi.1,hi.2] using X.initial_v)
    (fun _ ht => M.complete_defect D hD hM hx ht)
  intro t ht
  constructor
  · exact (h t ht).1
  · have hv := div_le_div_of_nonneg_right (h t ht).2 (by positivity : 0≤600*(D.alpha:ℝ))
    exact hv

theorem Profile.certifies (M : Profile) (D : Data) (hD : D.Valid) (hM : M.Valid D)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x)
    (X : Motion (D.alpha:ℝ) (direction x)) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖X.p t-D.position x t‖≤(M.positionError:ℝ) ∧
      ‖X.v t-D.velocity x t‖/(600*(D.alpha:ℝ))≤(M.velocityError D:ℝ) := by
  have h := M.certifies_curve D hD hM hx X
  intro t ht
  have hp := PolynomialOrder.value_le_endpoint M.envelope hM.envelope.2.1 ht
  have hv := PolynomialOrder.value_le_endpoint (differentiate M.envelope) hM.envelope.2.2.1 ht
  have heP := PolynomialOrder.value_at_rational M.envelope 1
  have heV := PolynomialOrder.value_at_rational (differentiate M.envelope) 1
  simp only [Rat.cast_one] at heP heV
  constructor
  · exact (h t ht).1.trans (by simpa only [heP,Profile.positionError] using hp)
  · have ha : 0≤600*(D.alpha:ℝ) := by exact_mod_cast (mul_nonneg (by norm_num : (0:ℚ)≤600) hD.alpha_pos.le)
    have hd := div_le_div_of_nonneg_right hv ha
    exact (h t ht).2.trans (by
      simpa only [heV,Profile.velocityError,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using hd)

theorem Profile.physical_prediction (M : Profile) (D : Data) (hD : D.Valid) (hM : M.Valid D)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x) :
    ∃ X : Motion (D.alpha:ℝ) (direction x), ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-D.position x t‖≤(M.positionError:ℝ) ∧
      ‖X.v t-D.velocity x t‖/(600*(D.alpha:ℝ))≤(M.velocityError D:ℝ) :=
  ⟨D.trajectory hD x hx,M.certifies D hD hM hx (D.trajectory hD x hx)⟩

end
end GNC.OrbitalComparison.PointingCapTimeCertificate
