import GNC.Applications.OrbitalComparison.VaryingRateData.Retained
import GNC.Applications.OrbitalComparison.VaryingRateData.Quartic
import GNC.Analysis.PointingPolynomialEvaluation
import GNC.Analysis.PredictionComparison

/-! A comparison of two concrete predictors for the same physical burn.
The endpoint witness includes certified trigonometric evaluation error.
It proves an actual accuracy comparison, not a ranking of all STT methods.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace GNC.OrbitalComparison.VaryingRateData.Comparison
open PolynomialODE ParameterPolynomial VaryingRateCertificate Set

def angle : ℚ := 1/10
def difference (i : Fin 3) : Expr 2 :=
  .add (PointingPolynomialEvaluation.expression (Retained.record.q i) 1)
    (.constant (-rationalValue (Quartic.record.q i) ![angle,0,0] 1))
def lower (i : Fin 3) : ℚ :=
  |(difference i).ratValue (CircleEvaluation.center angle)|-
    (difference i).differenceMajorant (fun _ => 1) (fun _ => CircleEvaluation.radius angle)

theorem input_region : ∀ i : Fin 2,
    |CircleEvaluation.center angle i|+CircleEvaluation.radius angle≤1 := by decide +kernel

theorem lower_nonnegative : ∀ i : Fin 3, 0≤lower i := by decide +kernel
theorem computed_separation : (3*Retained.record.positionError)^2<
    (lower 0)^2+(lower 1)^2+(lower 2)^2 := by decide +kernel

theorem certificate_order : Retained.record.positionError<Quartic.record.positionError := by decide +kernel

noncomputable section

theorem difference_value (i : Fin 3) :
    (difference i).value (CircleEvaluation.inputs (angle:ℝ))=
      (Retained.record.displacement (angle:ℝ) 1-Quartic.record.displacement (angle:ℝ) 1) i := by
  rw [difference,Expr.value,PointingPolynomialEvaluation.expression_value]
  simp only [Expr.value,Rat.cast_neg,rationalValue_cast,Rat.cast_one]
  have hc : (fun j : Fin 3 => ((![angle,0,0] j : ℚ):ℝ))=![(angle:ℝ),0,0] := by
    ext j
    fin_cases j <;> simp
  rw [hc,←sub_eq_add_neg]
  change ParameterPolynomial.value (Retained.record.q i) ![Real.sin (angle:ℝ),0,1-Real.cos (angle:ℝ)] 1-
      ParameterPolynomial.value (Quartic.record.q i) ![(angle:ℝ),0,0] 1=_
  simp only [Data.displacement,PointingCapPolynomial.vectorValue,SpatialBurn.pack_eq,
    WithLp.ofLp_sub,WithLp.ofLp_toLp,Pi.sub_apply]
  fin_cases i <;> rfl

theorem scalar_separation (i : Fin 3) :
    (lower i:ℝ)≤|(Retained.record.displacement (angle:ℝ) 1-Quartic.record.displacement (angle:ℝ) 1) i| := by
  have hb := (difference i).evaluation_error (CircleEvaluation.center angle)
    (fun _ => 1) (fun _ => CircleEvaluation.radius angle)
    (fun _ => by norm_num) (fun _ => by unfold CircleEvaluation.radius; positivity)
    input_region (CircleEvaluation.inputs (angle:ℝ)) (CircleEvaluation.input_error angle)
  have ht := abs_sub_le ((difference i).ratValue (CircleEvaluation.center angle):ℝ)
    ((difference i).value (CircleEvaluation.inputs (angle:ℝ))) 0
  rw [abs_sub_comm] at hb
  simp only [sub_zero] at ht
  rw [←difference_value]
  simp only [lower,Rat.cast_sub,Rat.cast_abs]
  linarith

theorem displacement_separation :
    3*(Retained.record.positionError:ℝ)<
      ‖Retained.record.displacement (angle:ℝ) 1-Quartic.record.displacement (angle:ℝ) 1‖ := by
  let d := Retained.record.displacement (angle:ℝ) 1-Quartic.record.displacement (angle:ℝ) 1
  have hs (i : Fin 3) : (lower i:ℝ)^2≤(d i)^2 := by
    have hl : (0:ℝ)≤(lower i:ℝ) := by exact_mod_cast lower_nonnegative i
    have hb := scalar_separation i
    change (lower i:ℝ)≤|d i| at hb
    nlinarith [sq_abs (d i),abs_nonneg (d i)]
  have hn := SpatialBurn.pack_norm_sq (d 0) (d 1) (d 2)
  rw [VaryingRateFrame.pack_components] at hn
  have hg : (3*(Retained.record.positionError:ℝ))^2<
      (lower 0:ℝ)^2+(lower 1:ℝ)^2+(lower 2:ℝ)^2 := by exact_mod_cast computed_separation
  change _<‖d‖
  nlinarith [hs 0,hs 1,hs 2,norm_nonneg d]

theorem position_separation :
    3*(Retained.record.positionError:ℝ)<
      ‖Retained.record.position (angle:ℝ) 1-Quartic.record.position (angle:ℝ) 1‖ := by
  have he : Retained.record.position (angle:ℝ) 1-Quartic.record.position (angle:ℝ) 1=
      VaryingRateFrame.turn (Retained.record.model.phase 1)
        (Retained.record.displacement (angle:ℝ) 1-Quartic.record.displacement (angle:ℝ) 1) := by
    change (Retained.record.model.reference 1+
        VaryingRateFrame.turn (Retained.record.model.phase 1) (Retained.record.displacement (angle:ℝ) 1))-
      (Retained.record.model.reference 1+
        VaryingRateFrame.turn (Retained.record.model.phase 1) (Quartic.record.displacement (angle:ℝ) 1))=_
    rw [map_sub]
    abel
  rw [he,VaryingRateFrame.turn_norm]
  exact displacement_separation

/-- At θ=0.1 rad and t=1200 s, the stored quartic angle jet has more than
twice the actual position error of the retained-pointing predictor.
Existence of this full-gravity motion is supplied by Retained.physical_prediction. -/
theorem actual_error_strict (X : VaryingRateBurn.Motion Retained.record.model (angle:ℝ)) :
    2*‖X.p 1-Retained.record.position (angle:ℝ) 1‖<‖X.p 1-Quartic.record.position (angle:ℝ) 1‖ := by
  have hp := (Retained.physical_prediction (θ := (angle:ℝ)) (by norm_num [angle])).2 X 1 (by constructor <;> norm_num)
  simpa using FiniteAngleComparison.certified_separation (X.p 1)
    (Retained.record.position (angle:ℝ) 1) (Quartic.record.position (angle:ℝ) 1)
    (k := 2) (by norm_num) hp.1 (by convert position_separation using 1 <;> norm_num)

end
end GNC.OrbitalComparison.VaryingRateData.Comparison
