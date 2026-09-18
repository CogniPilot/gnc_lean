import GNC.Applications.OrbitalComparison.TDSTTWitness
import GNC.Analysis.PolynomialObstruction
import GNC.Analysis.PolynomialLine

/-! Full-gravity obstruction for every quadratic Cartesian pointing map.
Four collinear inputs annihilate the entire quadratic class, including full
rank and arbitrary fitted coefficients. The physical sample uncertainty is
supplied by the existing Lie certificate and its checked output remainder.
Higher order, subdivision and nonpolynomial force features escape this class.
-/
namespace GNC.OrbitalComparison.TDSTTQuadraticObstruction
open TDSTTData ParameterPolynomial LieSTTOutput Set Matrix
set_option maxHeartbeats 0

def nodes : Fin 4 → ℚ := ![-1/10,-1/20,1/20,1/10]
def weights : Fin 4 → ℚ := ![-1/6,1/3,-1/3,1/6]
def points (i : Fin 4) : Fin 3 → ℚ := ![0,nodes i,0]
def reported (i : Fin 4) : ℚ := 7000000 * rationalValue
  (LieRadiusQuadraticPolynomial.displacement Lie2.physicalInput 2) (points i) 1
def sampleError : ℚ := Lie2.positionUpper + 7000000 * TDSTTWitness.reconstructionError
def lowerBound : ℚ := |∑ i, weights i * reported i| - sampleError
/-- Round the derived lower bound down to tenths of a millimetre. -/
def displayLower_mm : ℚ := (⌊(10000:ℚ)*lowerBound⌋:ℚ)/10
def displayLower_m : ℚ := displayLower_mm/1000

theorem moments : ∀ k : Fin 3, ∑ i, weights i * nodes i ^ (k:ℕ) = 0 := by decide +kernel
theorem variation : ∑ i, |weights i| = 1 := by decide +kernel
theorem display_checked : displayLower_mm = 12/5 ∧ displayLower_m < lowerBound := by
  decide +kernel
theorem millimetre_below_lower : (1/1000:ℚ) < lowerBound := by decide +kernel

noncomputable section
def inputs (i : Fin 4) : Vec3 := fun j => (points i j:ℝ)
def direction : Fin 3 → ℝ := ![0,1,0]
def referencePosition : SpatialBurn.E3 := WithLp.toLp 2 (JointErrorData.exactReference 1)
def approximatePosition (i : Fin 4) : SpatialBurn.E3 := referencePosition +
  WithLp.toLp 2 (LieRadiusQuadratic.apply (inputs i)
    (value3 Lie2.physicalInput.rho (inputs i) 1))
def deviation (p : SpatialBurn.E3) : SpatialBurn.E3 := (7000000:ℝ) • (p-referencePosition)

theorem admissible (i : Fin 4) :
    inputs i 0^2 + inputs i 1^2 + inputs i 2^2 ≤ ((1/10:ℚ):ℝ)^2 := by
  fin_cases i <;> norm_num [inputs,points,nodes,vecHead,vecTail,Matrix.cons_val_two]

theorem inputs_line (i : Fin 4) : inputs i = fun j => direction j * (nodes i:ℝ) := by
  ext j
  fin_cases j <;> simp [inputs,points,direction]

theorem moments_real : ∀ k ≤ 2, ∑ i, (weights i:ℝ)*(nodes i:ℝ)^k = 0 := by
  intro k hk
  exact_mod_cast moments ⟨k,by omega⟩
theorem variation_real : ∑ i, |(weights i:ℝ)| = 1 := by exact_mod_cast variation

theorem reported_cast (i : Fin 4) :
    (reported i:ℝ) = (deviation (approximatePosition i)).ofLp 2 := by
  simp only [reported,Rat.cast_mul,Rat.cast_ofNat,rationalValue_cast,Rat.cast_one]
  have h := LieRadiusQuadraticPolynomial.displacement_value Lie2.physicalInput (inputs i) 1
  change 7000000 * value (LieRadiusQuadraticPolynomial.displacement Lie2.physicalInput 2)
    (inputs i) 1 = _
  rw [show value (LieRadiusQuadraticPolynomial.displacement Lie2.physicalInput 2)
      (inputs i) 1 = (LieRadiusQuadratic.apply (inputs i)
        (value3 Lie2.physicalInput.rho (inputs i) 1)) 2 from congrFun h 2]
  simp [deviation,approximatePosition]

theorem reconstruction_bound (i : Fin 4) :
    ‖Lie2.candidatePosition (inputs i) 1-approximatePosition i‖ ≤
      (TDSTTWitness.reconstructionError:ℝ) := by
  have hs := (Lie2.attitude_bound (admissible i)).1
  have hp := Lie2.displacement_uniform (admissible i)
    (by constructor <;> norm_num : (1:ℝ) ∈ Icc 0 1)
  have hσ : (0:ℝ)≤Lie2.sigma := by norm_num [Lie2.sigma]
  have h := (LieRadiusQuadratic.error_bound (inputs i)
    (value3 Lie2.physicalInput.rho (inputs i) 1)).trans
    (mul_le_mul (LieRadiusQuadratic.tail_mono (enorm_nonneg _) hs) hp
      (enorm_nonneg _) (LieRadiusQuadratic.tail_nonnegative hσ))
  have he : (TDSTTWitness.reconstructionError:ℝ) =
      LieRadiusQuadratic.tail (Lie2.sigma:ℝ)*(Lie2.displacementMaximum:ℝ) := by
    simp only [TDSTTWitness.reconstructionError,Lie2.jacobianTail,LieRadiusQuadratic.tail,
      Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  rw [he]
  simpa only [Lie2.candidatePosition,approximatePosition,referencePosition,
    add_sub_add_left_eq_sub,LieRadiusFrame.left,Lie2.polynomial_value] using h

theorem physical_sample (i : Fin 4) (X : Lie2.Motion (inputs i)) :
    |(deviation (X.p 1)).ofLp 2-(reported i:ℝ)| ≤ (sampleError:ℝ) := by
  rw [reported_cast]
  have hp := ((Lie2.physical_prediction (admissible i)).2 X 1 (by norm_num)).1
  have ht := norm_sub_le_norm_sub_add_norm_sub (X.p 1)
    (Lie2.candidatePosition (inputs i) 1) (approximatePosition i)
  have hr := reconstruction_bound i
  have hc := PiLp.norm_apply_le (deviation (X.p 1)-deviation (approximatePosition i)) (2:Fin 3)
  have hn : ‖deviation (X.p 1)-deviation (approximatePosition i)‖ =
      7000000*‖X.p 1-approximatePosition i‖ := by
    simp only [deviation,←smul_sub,sub_sub_sub_cancel_right,norm_smul,Real.norm_eq_abs]
    norm_num
  rw [hn] at hc
  simp only [PiLp.sub_apply,Real.norm_eq_abs] at hc
  simp only [sampleError,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat]
  linarith

theorem coordinate_error_ge (X : ∀ i, Lie2.Motion (inputs i))
    (p : Polynomial ℝ) (hp : p.natDegree≤2) :
    ∃ i, (lowerBound:ℝ) ≤ |(deviation ((X i).p 1)).ofLp 2-p.eval (nodes i:ℝ)| := by
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 4 => |(deviation ((X i).p 1)).ofLp 2-p.eval (nodes i:ℝ)|) (by simp)
  have hb := PolynomialObstruction.error_lower_bound
    (fun i => (nodes i:ℝ)) (fun i => (weights i:ℝ))
    (fun i => (deviation ((X i).p 1)).ofLp 2) (fun i => (reported i:ℝ))
    (fun _ => (sampleError:ℝ)) moments_real variation_real
    (fun i => physical_sample i (X i)) p hp (fun j => hi j (by simp))
  have he : (∑ i, |(weights i:ℝ)| * (sampleError:ℝ))=(sampleError:ℝ) := by
    rw [←Finset.sum_mul,variation_real,one_mul]
  rw [he] at hb
  exact ⟨i,by simpa only [lowerBound,Rat.cast_sub,Rat.cast_abs,Rat.cast_sum,Rat.cast_mul] using hb⟩

/-- Any quadratic Cartesian position map has a physical endpoint error
above 2.4 mm at one of four admitted inputs. Coefficients and rank are arbitrary. -/
theorem cartesian_quadratic_obstruction (X : ∀ i, Lie2.Motion (inputs i))
    (p : Fin 3 → MvPolynomial (Fin 3) ℝ) (hp : (p 2).totalDegree≤2) :
    ∃ i, (displayLower_m:ℝ) < ‖deviation ((X i).p 1)-
      WithLp.toLp 2 (fun j => MvPolynomial.eval (inputs i) (p j))‖ := by
  obtain ⟨i,hi⟩ := coordinate_error_ge X (PolynomialLine.restrict direction (p 2))
    ((PolynomialLine.degree direction (p 2)).trans hp)
  rw [PolynomialLine.eval,←inputs_line] at hi
  have hc := PiLp.norm_apply_le (deviation ((X i).p 1)-
    WithLp.toLp 2 (fun j : Fin 3 => MvPolynomial.eval (inputs i) (p j))) (2:Fin 3)
  have hl : (displayLower_m:ℝ)<(lowerBound:ℝ) := by exact_mod_cast display_checked.2
  exact ⟨i,hl.trans_le (hi.trans (by simpa only [PiLp.sub_apply,Real.norm_eq_abs] using hc))⟩

/-- The existing physical existence certificate constructs each witness motion. -/
def trajectory (i : Fin 4) : Lie2.Motion (inputs i) :=
  Classical.choose (Lie2.exists_motion (admissible i))

theorem physical_comparison (p : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hp : (p 2).totalDegree≤2) :
    ∃ i, (displayLower_m:ℝ) < ‖deviation ((trajectory i).p 1)-
        WithLp.toLp 2 (fun j => MvPolynomial.eval (inputs i) (p j))‖ ∧
      7000000*‖(trajectory i).p 1-Lie2.candidatePosition (inputs i) 1‖ < 1/1000 := by
  obtain ⟨i,hi⟩ := cartesian_quadratic_obstruction trajectory p hp
  have h := ((Lie2.physical_prediction (admissible i)).2 (trajectory i) 1 (by norm_num)).1
  have he : (Lie2.positionUpper:ℝ)<(1/1000:ℝ) := by
    have hq : (Lie2.positionUpper:ℝ)<((1/1000:ℚ):ℝ) := by
      exact_mod_cast TDSTTWitness.lie_millimetre_checked
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hq
    exact hq
  exact ⟨i,hi,h.trans_lt he⟩

/-- A one-millimetre endpoint guarantee requires at least cubic dependence
on the rotation-vector inputs in this fixed Cartesian polynomial chart. -/
theorem required_degree (p : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (h : ∀ i, ‖deviation ((trajectory i).p 1)-
      WithLp.toLp 2 (fun j => MvPolynomial.eval (inputs i) (p j))‖ ≤ (1/1000:ℝ)) :
    3≤(p 2).totalDegree := by
  by_contra hn
  obtain ⟨i,hi,_⟩ := physical_comparison p (by omega)
  have hd : (1/1000:ℝ)<(displayLower_m:ℝ) := by
    have he : displayLower_m=12/5000 := by rw [displayLower_m,display_checked.1]; norm_num
    rw [he]; norm_num
  linarith [h i]

end
end GNC.OrbitalComparison.TDSTTQuadraticObstruction
