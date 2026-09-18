import GNC.Applications.OrbitalComparison.LieRadiusData.Bounds
import GNC.Applications.OrbitalComparison.LieRadiusData.Envelope

/-! Complete direct Lie-coordinate certificate for the full inverse-square
120-second burn. Existence is reused for the same physical model; the new
defect, radius floor and error envelope do not expand a Cartesian trajectory
polynomial. These are bounds on a continuum of angles and times, not samples.
-/
namespace GNC.OrbitalComparison.LieRadiusData
open LieRadiusPolynomial PointingCapPolynomial SpatialBurn VaryingRateBurn
open VaryingRateFrame Set Matrix Planning.PolynomialKernel

theorem initial_checked :
    (∀ i, initialZero (input.rho i)) ∧
    (∀ i, initialZero (PointingCapPolynomial.derivative input.rho i)) := by
  constructor <;> intro i <;> fin_cases i <;> decide +kernel

noncomputable section

theorem initial (θ : ℝ) : input.position θ 0=input.model.reference 0 ∧
    input.velocity θ 0=input.model.referenceVelocity 0 := by
  have hp : input.translation θ 0=0 := by
    ext i
    fin_cases i <;> simp [Input.translation,vectorValue,pack_eq,
      initial_value _ (initial_checked.1 _) _]
  have hv : input.translationVelocity θ 0=0 := by
    ext i
    fin_cases i <;> simp [Input.translationVelocity,vectorValue,pack_eq,
      initial_value _ (initial_checked.2 _) _]
  constructor
  · simp only [Input.position,LieRadiusFrame.position,hp,map_zero,add_zero]
  · simp only [Input.velocity,LieRadiusFrame.velocity,hp,hv,map_zero,add_zero]

theorem candidate_radius {θ t : ℝ} (hθ : |θ| ≤ (sigma:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) :
    (input.r:ℝ)-2*(regionRadius:ℝ)+(regionRadius:ℝ) ≤ ‖input.position θ t‖ := by
  have hr := real_checks.2.1
  have hφ : enorm (θ • LieSTTOutput.axis (input.model.phase t))<2*Real.pi := by
    simpa only [enorm_smul,Gravity.unit_enorm _ (LieSTTOutput.axis_unit _),mul_one] using chart_bound hθ
  have hd := (LieRadiusFrame.left_norm _ hφ (input.translation θ t)).trans (translation_bound hθ ht)
  have hn := norm_sub_le (input.position θ t)
    (turn (input.model.phase t)
      (LieRadiusFrame.left (θ • LieSTTOutput.axis (input.model.phase t)) (input.translation θ t)))
  have he : input.position θ t-turn (input.model.phase t)
      (LieRadiusFrame.left (θ • LieSTTOutput.axis (input.model.phase t)) (input.translation θ t))=
      input.model.reference t := by
    rw [Input.position,LieRadiusFrame.position_body,add_sub_cancel_right]
  rw [he,input.model.reference_norm hr.le,turn_norm] at hn
  change (input.r:ℝ) ≤ _ at hn
  linarith

/-- All times in the burn and all pointing angles in the stated interval
are covered, with physical gravity and exact exponential reconstruction. -/
theorem certifies {θ : ℝ} (hθ : |θ| ≤ (sigma:ℝ)) (X : Motion input.model θ) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖X.p t-input.position θ t‖ ≤
      ((evaluate envelope 1:ℚ):ℝ) ∧
      ‖X.v t-input.velocity θ t‖/120 ≤ ((evaluate (differentiate envelope) 1/120:ℚ):ℝ) := by
  obtain ⟨hμ,hr,hσ,hZ,hH,hH1,hU,hδ,hC,hS,hB,hE,hP,hPr⟩ := real_checks
  have hclose : PolynomialOrder.value forcing 1*
      PolynomialSupersolution.value (gain:ℝ) 1 < (regionRadius:ℝ) := by
    have hh : ((evaluate forcing 1:ℚ):ℝ)*(HarmonicCertificate.positionGain gain:ℝ)<(regionRadius:ℝ) := by
      exact_mod_cast closure_checked
    have he := PolynomialOrder.value_at_rational forcing 1
    norm_num only [Rat.cast_one] at he
    simpa only [he,HarmonicCertificate.positionGain_cast] using hh
  have hgain : 1*(2*(input.μ:ℝ)/((input.r:ℝ)-2*(regionRadius:ℝ))^3) ≤ (gain:ℝ) := by
    have hg : (exactGain:ℝ) ≤ (gain:ℝ) := by exact_mod_cast gain_checked.2.2
    simpa only [exactGain,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_pow,Rat.cast_ofNat,one_mul] using hg
  have hb := Gravity.polynomial_prediction (input.μ:ℝ) 1 hμ (by norm_num)
    X.p X.v (input.position θ) (input.velocity θ) (input.acceleration θ) (input.model.thrust θ)
    forcing envelope envelope_checked gain_checked.1 gain_checked.2.1
    (r := (input.r:ℝ)-2*(regionRadius:ℝ)) (by linarith) hclose hgain
    (fun _ ht => candidate_radius hθ ht) X.continuous_p X.continuous_v
    (continuous_iff_continuousAt.mpr fun t => (input.position_derivative θ t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (input.velocity_derivative hr θ t).continuousAt)
    X.derivative_p
    (fun t ht => by simpa only [Model.acceleration,Input.model,one_smul] using X.derivative_v t ht)
    (fun t _ => input.position_derivative θ t) (fun t _ => input.velocity_derivative hr θ t)
    (X.initial_p.trans (initial θ).1.symm) (X.initial_v.trans (initial θ).2.symm)
    (fun t ht => by
      have hd := (physical_defect hθ ht).trans (forcing_dominates ht.1)
      simpa only [Model.acceleration,Input.model,one_smul,norm_sub_rev] using hd)
  intro t ht
  constructor
  · exact (hb t ht).1
  · have hv := div_le_div_of_nonneg_right (hb t ht).2 (by norm_num : (0:ℝ) ≤ 120)
    simpa only [Rat.cast_div,Rat.cast_ofNat] using hv

/-- Nonvacuous uniform physical certificate: a full-gravity solution exists
and every solution satisfying this model has the stated error bounds. -/
theorem physical_prediction {θ : ℝ} (hθ : |θ| ≤ (sigma:ℝ)) :
    (∃ X : Motion input.model θ, True) ∧
    (∀ X : Motion input.model θ, ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-input.position θ t‖ ≤ (626/1000000:ℝ) ∧
      ‖X.v t-input.velocity θ t‖/120 ≤ (212/10000000:ℝ)) := by
  constructor
  · rw [model_eq]
    obtain ⟨X,hX⟩ := LieSTTData.Lie3.record.exists_motion LieSTTData.Lie3.valid hθ
    exact ⟨X,trivial⟩
  · intro X t ht
    have hb := certifies hθ X t ht
    have hd : ((evaluate envelope 1:ℚ):ℝ) ≤ (626/1000000:ℝ) ∧
        ((evaluate (differentiate envelope) 1/120:ℚ):ℝ) ≤ (212/10000000:ℝ) := by
      constructor
      · have hd : ((evaluate envelope 1:ℚ):ℝ) ≤ ((626/1000000:ℚ):ℝ) :=
          Rat.cast_le.mpr displayed_bounds.1
        simpa only [Rat.cast_div,Rat.cast_ofNat] using hd
      · have hd : ((evaluate (differentiate envelope) 1/120:ℚ):ℝ) ≤ ((212/10000000:ℚ):ℝ) :=
          Rat.cast_le.mpr displayed_bounds.2
        simpa only [Rat.cast_div,Rat.cast_ofNat] using hd
    exact ⟨hb.1.trans hd.1,hb.2.trans hd.2⟩

end
end GNC.OrbitalComparison.LieRadiusData
