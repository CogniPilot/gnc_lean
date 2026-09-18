import GNC.Applications.OrbitalComparison.TDSTTComparison
import GNC.Analysis.ParameterPolynomialEvaluation

/-! A proved actual-error separation for the two concrete rank-two queries.
The Cartesian lower bound uses a rational output difference and the Lie
physical certificate, not an assumed numerical integration accuracy. -/
namespace GNC.OrbitalComparison.TDSTTWitness
open TDSTTData ParameterPolynomial LieSTTOutput Set Matrix

def witnessQ : Fin 3 → ℚ := ![3/50,2/25,0]
def difference : Coefficients := subtract (Cartesian2.position 1)
  (LieRadiusQuadraticPolynomial.displacement Lie2.physicalInput 1)
def reconstructionError : ℚ := Lie2.jacobianTail*Lie2.displacementMaximum

set_option maxHeartbeats 0 in
theorem separation_checked :
    7000000*rationalValue difference witnessQ 1<
      -(1/4+Lie2.positionUpper+7000000*reconstructionError) := by
  decide +kernel

theorem lie_millimetre_checked : Lie2.positionUpper<1/1000 := by decide +kernel

noncomputable section
def witness : Vec3 := fun i => (witnessQ i:ℝ)

theorem witness_admissible : witness 0^2+witness 1^2+witness 2^2≤((1/10:ℚ):ℝ)^2 := by
  norm_num [witness,witnessQ,vecHead,vecTail]
  rfl

def approximatePosition : SpatialBurn.E3 :=
  WithLp.toLp 2 (JointErrorData.exactReference 1)+
    WithLp.toLp 2 (LieRadiusQuadratic.apply witness (value3 Lie2.physicalInput.rho witness 1))

theorem difference_value :
    ((Cartesian2.candidatePosition witness 1-approximatePosition).ofLp 1)=
      (rationalValue difference witnessQ 1:ℝ) := by
  rw [rationalValue_cast]
  norm_num only [Rat.cast_one]
  rw [difference,value_subtract]
  have hd := LieRadiusQuadraticPolynomial.displacement_value Lie2.physicalInput witness 1
  change _=value (Cartesian2.position 1) witness 1-
    value (LieRadiusQuadraticPolynomial.displacement Lie2.physicalInput 1) witness 1
  rw [show value (LieRadiusQuadraticPolynomial.displacement Lie2.physicalInput 1) witness 1=
    (LieRadiusQuadratic.apply witness (value3 Lie2.physicalInput.rho witness 1)) 1 from congrFun hd 1]
  simp only [Cartesian2.candidatePosition,approximatePosition,Cartesian2.polynomial_value,
    add_sub_add_left_eq_sub]
  rfl

theorem reconstruction_bound :
    ‖Lie2.candidatePosition witness 1-approximatePosition‖≤(reconstructionError:ℝ) := by
  have hs := (Lie2.attitude_bound witness_admissible).1
  have hp := Lie2.displacement_uniform witness_admissible (by constructor <;> norm_num : (1:ℝ) ∈ Icc 0 1)
  have hσ : (0:ℝ)≤Lie2.sigma := by norm_num [Lie2.sigma]
  have h := (LieRadiusQuadratic.error_bound witness (value3 Lie2.physicalInput.rho witness 1)).trans
    (mul_le_mul (LieRadiusQuadratic.tail_mono (enorm_nonneg witness) hs) hp
      (enorm_nonneg _) (LieRadiusQuadratic.tail_nonnegative hσ))
  have he : (reconstructionError:ℝ)=LieRadiusQuadratic.tail (Lie2.sigma:ℝ)*(Lie2.displacementMaximum:ℝ) := by
    simp only [reconstructionError,Lie2.jacobianTail,LieRadiusQuadratic.tail,
      Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  rw [he]
  simpa only [Lie2.candidatePosition,approximatePosition,add_sub_add_left_eq_sub,
    LieRadiusFrame.left,Lie2.polynomial_value] using h

theorem signed_difference_bound :
    -((Cartesian2.candidatePosition witness 1-approximatePosition).ofLp 1)≤
      ‖Cartesian2.candidatePosition witness 1-approximatePosition‖ := by
  exact (neg_le_abs _).trans (by
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (Cartesian2.candidatePosition witness 1-approximatePosition) (1 : Fin 3))

/-- At the explicit 0.1-rad pointing vector, every physical motion has
Cartesian endpoint error above 25 cm, while Lie is below 1 mm. -/
theorem actual_error_separation (X : Lie2.Motion witness) :
    (1/4:ℝ)<7000000*‖X.p 1-Cartesian2.candidatePosition witness 1‖ ∧
      7000000*‖X.p 1-Lie2.candidatePosition witness 1‖<1/1000 := by
  have hL := ((Lie2.physical_prediction witness_admissible).2 X 1
    (by constructor <;> norm_num)).1
  have hs : (7000000:ℝ)*(rationalValue difference witnessQ 1:ℝ)<
      -((1/4:ℝ)+(Lie2.positionUpper:ℝ)+7000000*(reconstructionError:ℝ)) := by
    have h : ((7000000*rationalValue difference witnessQ 1:ℚ):ℝ)<
        ((-(1/4+Lie2.positionUpper+7000000*reconstructionError):ℚ):ℝ) := by
      exact_mod_cast separation_checked
    push_cast at h
    exact h
  rw [←difference_value] at hs
  have hc := signed_difference_bound
  have he := reconstruction_bound
  have htri := norm_sub_le_norm_sub_add_norm_sub (Cartesian2.candidatePosition witness 1)
    (X.p 1) approximatePosition
  have htri2 := norm_sub_le_norm_sub_add_norm_sub (X.p 1)
    (Lie2.candidatePosition witness 1) approximatePosition
  rw [norm_sub_rev (Cartesian2.candidatePosition witness 1) (X.p 1)] at htri
  have hm : (Lie2.positionUpper:ℝ)<((1/1000:ℚ):ℝ) := by exact_mod_cast lie_millimetre_checked
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hm
  exact ⟨by linarith, hL.trans_lt hm⟩

/-- This ratio concerns the actual errors of these two specific predictors
at one admitted input; it is not a lower bound for every Cartesian scheme. -/
theorem actual_error_ratio (X : Lie2.Motion witness) :
    250*(7000000*‖X.p 1-Lie2.candidatePosition witness 1‖)<
      7000000*‖X.p 1-Cartesian2.candidatePosition witness 1‖ := by
  have h := actual_error_separation X
  linarith

theorem exists_actual_error_separation : ∃ X : Lie2.Motion witness,
    (1/4:ℝ)<7000000*‖X.p 1-Cartesian2.candidatePosition witness 1‖ ∧
      7000000*‖X.p 1-Lie2.candidatePosition witness 1‖<1/1000 := by
  obtain ⟨X,_⟩ := Lie2.exists_motion witness_admissible
  exact ⟨X,actual_error_separation X⟩

end
end GNC.OrbitalComparison.TDSTTWitness
