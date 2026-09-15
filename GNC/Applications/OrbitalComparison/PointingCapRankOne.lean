import GNC.Analysis.RankOneCurvature
import GNC.Analysis.ParameterPolynomialCertificate
import GNC.Applications.OrbitalComparison.PointingCapObstruction
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerTime12Burn1200

/-! A physical obstruction for every degree-four transverse expansion whose
quadratic tensor is rank one. The four admissible witness directions depend
on the quadratic input direction; all coefficients and the cubic/quartic
directions remain arbitrary. This covers the endpoint form of R1-ODSTT,
not uncompressed STTs or nonlinear input charts. -/
namespace GNC.OrbitalComparison.PointingCapRankOne
open PointingCapCertificate PointingCapBurn SpatialBurn ParameterPolynomial Set
open PointingCapDiskData.DiskHornerTime12Burn1200
set_option maxHeartbeats 0

abbrev data := PointingCapData.HornerTime12Burn1200.data

/-- Two rational half-angle nodes, inside the physical transverse radius 0.1.
They are proof witnesses, not restrictions imposed on the physical family. -/
def a : ℚ := 40/401
def b : ℚ := 80/1601
def ca : ℚ := 2/401
def cb : ℚ := 2/1601
def weight : ℚ := a^4/(a^4+b^4)
def curvatureMoment : ℚ := weight*cb-(1-weight)*ca
def quadraticMoment : ℚ := weight*b^2-(1-weight)*a^2

/-- Exact endpoint coefficients extracted from the already certified predictor. -/
def radial : ℚ := -10968241714654930170363/1152921504606846976
def vv : ℚ := 2068701924281250281/576460752303423488
def linear : ℚ := 5000180278018077154379/576460752303423488
def mixed : ℚ := 4154504018392029/1125899906842624
def uu : ℚ := 1442624815541560853/576460752303423488
def endpoint : Coefficients :=
  [⟨0,0,1,[radial]⟩,⟨0,2,0,[vv]⟩,⟨1,0,0,[linear]⟩,
   ⟨1,0,1,[mixed]⟩,⟨2,0,0,[uu]⟩]

theorem endpoint_extraction : atTime (data.q 0) 1=endpoint := by decide +kernel
theorem weight_range : 0≤weight ∧ weight≤1 := by decide +kernel
theorem quartic_balance : weight*b^4=(1-weight)*a^4 := by decide +kernel
theorem quadratic_nonnegative : 0≤quadraticMoment := by decide +kernel
theorem coefficient_order : 0≤uu ∧ 0≤vv ∧ uu≤vv := by decide +kernel

/-- The exact refined physical error budget; no extra allowance is added. -/
def physicalError : ℚ := bounds.positionError data
def witnessAmplitude : ℚ := -radial*curvatureMoment-quadraticMoment*vv
def lowerBound : ℚ := witnessAmplitude-physicalError
/-- Round the derived lower bound down to centimetres for display. -/
def displayLower_m : ℚ := (⌊100*lowerBound⌋:ℚ)/100
theorem display_value : displayLower_m=209/25 := by decide +kernel
theorem display_below : displayLower_m<lowerBound := by decide +kernel

noncomputable section

def nodes : Fin 4 → ℝ := RankOneCurvature.nodes (a:ℝ) (b:ℝ)
def weights : Fin 4 → ℝ := RankOneCurvature.weights (weight:ℝ)
def deficits : Fin 4 → ℝ := ![(cb:ℝ),(cb:ℝ),(ca:ℝ),(ca:ℝ)]
def inputs (w0 w1 : ℝ) (i : Fin 4) : Fin 3 → ℝ :=
  ![-w1*nodes i,w0*nodes i,deficits i]

theorem admissible {w0 w1 : ℝ} (hw : w0^2+w1^2=1) (i : Fin 4) :
    Admissible (data.sigma:ℝ) (inputs w0 w1 i) := by
  have hr (t : ℝ) : (-w1*t)^2+(w0*t)^2=t^2 := by nlinarith [sq_nonneg t]
  change 0≤deficits i ∧ deficits i≤1 ∧
    (-w1*nodes i)^2+(w0*nodes i)^2=2*deficits i-(deficits i)^2 ∧
    (-w1*nodes i)^2+(w0*nodes i)^2≤(((1/10:ℚ):ℝ))^2
  rw [hr]
  fin_cases i <;> norm_num [nodes,RankOneCurvature.nodes,deficits,a,b,ca,cb]

theorem endpoint_value (x : Fin 3 → ℝ) :
    value (data.q 0) x 1=(radial:ℝ)*x 2+(vv:ℝ)*x 1^2+
      (linear:ℝ)*x 0+(mixed:ℝ)*x 0*x 2+(uu:ℝ)*x 0^2 := by
  have h := value_atTime (data.q 0) 1 x 0
  rw [endpoint_extraction] at h
  simpa [endpoint,value,termValue,monomial,PolynomialOrder.value,
    Planning.PolynomialKernel.evaluate,add_assoc,mul_assoc] using h.symm

def reported (w0 w1 : ℝ) (i : Fin 4) : ℝ := value (data.q 0) (inputs w0 w1 i) 1

theorem witness_factorization (w0 w1 : ℝ) :
    (∑ i, weights i*reported w0 w1 i)=
      (radial:ℝ)*(curvatureMoment:ℝ)+
        (quadraticMoment:ℝ)*((uu:ℝ)*w1^2+(vv:ℝ)*w0^2) := by
  simp [reported,endpoint_value,weights,RankOneCurvature.weights,inputs,
    nodes,RankOneCurvature.nodes,deficits,Fin.sum_univ_four,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    curvatureMoment,quadraticMoment,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_one]
  ring

theorem witness_lower {w0 w1 : ℝ} (hw : w0^2+w1^2=1) :
    (witnessAmplitude:ℝ)≤|∑ i, weights i*reported w0 w1 i| := by
  rw [witness_factorization]
  have hu : (uu:ℝ)≤vv := by exact_mod_cast coefficient_order.2.2
  have hq : (0:ℝ)≤quadraticMoment := by exact_mod_cast quadratic_nonnegative
  have hb : (uu:ℝ)*w1^2+(vv:ℝ)*w0^2≤vv := calc
    _ ≤ (vv:ℝ)*w1^2+(vv:ℝ)*w0^2 := by
      linarith only [mul_le_mul_of_nonneg_right hu (sq_nonneg w1)]
    _ = (vv:ℝ) := by linear_combination (vv:ℝ)*hw
  have hm := mul_le_mul_of_nonneg_left hb hq
  have ha := neg_le_abs ((radial:ℝ)*(curvatureMoment:ℝ)+
    (quadraticMoment:ℝ)*((uu:ℝ)*w1^2+(vv:ℝ)*w0^2))
  simp only [witnessAmplitude,Rat.cast_sub,Rat.cast_neg,Rat.cast_mul]
  linarith

theorem candidate_frame (x : Fin 3 → ℝ) :
    PointingCapObstruction.framed (data.position x 1)=data.displacement x 1 := by
  change HarmonicFrame.turn (-2)
    ((PointingCapFrame.reference 2 1+HarmonicFrame.turn (2*1) (data.displacement x 1))-
       PointingCapFrame.reference 2 1)=_
  simp only [mul_one,add_sub_cancel_left,PointingCapObstruction.turn_inverse]

theorem physical_sample {w0 w1 : ℝ} (hw : w0^2+w1^2=1) (i : Fin 4)
    (X : Motion (data.alpha:ℝ) (direction (inputs w0 w1 i))) :
    |PointingCapObstruction.framed (X.p 1) 0-reported w0 w1 i|≤(physicalError:ℝ) := by
  have hp := (bounds.certifies data PointingCapData.HornerTime12Burn1200.valid
    (models.refinedBounds_sound original PointingCapData.HornerTime12Burn1200.valid valid)
      checks (admissible hw i) X 1 (by norm_num)).1
  have hn : ‖PointingCapObstruction.framed (X.p 1)-data.displacement (inputs w0 w1 i) 1‖≤
      (physicalError:ℝ) := by
    rw [←candidate_frame,PointingCapObstruction.frame_difference]
    exact hp
  have hc := (PiLp.norm_apply_le
    (PointingCapObstruction.framed (X.p 1)-data.displacement (inputs w0 w1 i) 1) 0).trans hn
  simpa only [reported,PiLp.sub_apply,Real.norm_eq_abs,Data.displacement,
    PointingCapPolynomial.vectorValue,pack_eq] using hc

/-- For every linear STM and every choice of the rank-one tensor factors,
some physical direction has this endpoint error. Unit norm is needed only
for the quadratic input direction; other orders may use any directions. -/
theorem coordinate_error_ge (l0 l1 q w0 w1 c z0 z1 d h0 h1 : ℝ)
    (hw : w0^2+w1^2=1)
    (X : ∀ i, Motion (data.alpha:ℝ) (direction (inputs w0 w1 i))) :
    ∃ i, (lowerBound:ℝ)≤|PointingCapObstruction.framed ((X i).p 1) 0-
      RankOneCurvature.predictor l0 l1 q w0 w1 c z0 z1 d h0 h1
        (inputs w0 w1 i 0) (inputs w0 w1 i 1)| := by
  have hv : ∑ i, |weights i|=1 := RankOneCurvature.variation
    (by exact_mod_cast weight_range.1) (by exact_mod_cast weight_range.2)
  have hp : ∑ i, weights i*RankOneCurvature.predictor l0 l1 q w0 w1 c z0 z1 d h0 h1
      (inputs w0 w1 i 0) (inputs w0 w1 i 1)=0 := by
    simp only [inputs,Matrix.cons_val_zero,Matrix.cons_val_one,RankOneCurvature.perpendicular_slice]
    exact RankOneCurvature.annihilates (by exact_mod_cast quartic_balance) _ _ _
  simpa only [lowerBound,Rat.cast_sub] using
    RankOneCurvature.physical_lower_bound weights
      (fun i => PointingCapObstruction.framed ((X i).p 1) 0) (reported w0 w1)
      (fun i => RankOneCurvature.predictor l0 l1 q w0 w1 c z0 z1 d h0 h1
        (inputs w0 w1 i 0) (inputs w0 w1 i 1)) hv hp
      (fun i => physical_sample hw i (X i)) (witness_lower hw)

/-- Existential physical solutions are supplied by the existing certificate.
Only the radial coordinate is restricted; the other predicted coordinates
can be arbitrary functions. Thus this also bounds Euclidean position error. -/
theorem physical_comparison (l0 l1 q w0 w1 c z0 z1 d h0 h1 : ℝ)
    (hw : w0^2+w1^2=1) (P : ℝ → ℝ → E3)
    (hP : ∀ u v, P u v 0=RankOneCurvature.predictor l0 l1 q w0 w1 c z0 z1 d h0 h1 u v) :
    ∃ i, Admissible (data.sigma:ℝ) (inputs w0 w1 i) ∧
      (displayLower_m:ℝ)<‖PointingCapObstruction.framed
        ((data.trajectory PointingCapData.HornerTime12Burn1200.valid
          (inputs w0 w1 i) (admissible hw i)).p 1)-
            P (inputs w0 w1 i 0) (inputs w0 w1 i 1)‖ := by
  obtain ⟨i,hi⟩ := coordinate_error_ge l0 l1 q w0 w1 c z0 z1 d h0 h1 hw
    (fun i => data.trajectory PointingCapData.HornerTime12Burn1200.valid
      (inputs w0 w1 i) (admissible hw i))
  have hc := PiLp.norm_apply_le
    (PointingCapObstruction.framed
      ((data.trajectory PointingCapData.HornerTime12Burn1200.valid
        (inputs w0 w1 i) (admissible hw i)).p 1)-
          P (inputs w0 w1 i 0) (inputs w0 w1 i 1)) 0
  simp only [PiLp.sub_apply,Real.norm_eq_abs,hP] at hc
  have hd : (displayLower_m:ℝ)<lowerBound := by exact_mod_cast display_below
  exact ⟨i,admissible hw i,hd.trans_le (hi.trans hc)⟩

end
end GNC.OrbitalComparison.PointingCapRankOne
