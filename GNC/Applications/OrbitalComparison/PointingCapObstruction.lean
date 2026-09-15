import GNC.Analysis.ParameterPolynomialEvaluation
import GNC.Analysis.PolynomialObstruction
import GNC.Analysis.PolynomialSlice
import GNC.Applications.OrbitalComparison.PointingCapData.ComponentTime12Burn1200

/-! A full-physics obstruction for cubic transverse-coordinate polynomials.
Five exact rational unit directions annihilate every cubic on the `v=0`
slice. The existing physical certificate supplies the complete sample-error
budget; no integration tolerance or sampled truth trajectory is assumed. -/
namespace GNC.OrbitalComparison.PointingCapObstruction
set_option maxHeartbeats 0
open PointingCapCertificate PointingCapBurn SpatialBurn Set
open PointingCapData.ComponentTime12Burn1200

/-- Rational half-angle witness nodes: `a = 2t/(1+t²)` at `t = 1/20`,
and `b` at `t = 1/28`. They lie near the edge and middle of the admitted
cap. These are freely chosen proof witnesses, not physical assumptions. -/
def a : ℚ := 40/401
def b : ℚ := 56/785
def points : Fin 5 → Fin 3 → ℚ :=
  ![![a,0,2/401],![-a,0,2/401],![b,0,2/785],![-b,0,2/785],![0,0,0]]
def nodes (i : Fin 5) : ℚ := points i 0
def weight : ℚ := b^2/(4*a^2)
def weights : Fin 5 → ℚ := ![weight,weight,-1/4,-1/4,1/2-2*weight]
def reported (i : Fin 5) : ℚ := ParameterPolynomial.rationalValue (data.q 0) (points i) 1
/-- Radial endpoint response coefficient multiplying the exact radial deficit
`c`. Evaluating at `(0,0,1)` extracts it from the reduced response; this is
coefficient extraction, not an additional physical pointing direction. -/
def radialResponse : ℚ := ParameterPolynomial.rationalValue (data.q 0) ![0,0,1] 1
def directionWitness : ℚ := ∑ i, weights i*points i 2
/-- The obstruction detects precisely the retained unit-direction curvature:
all other radial response terms vanish in this signed combination. -/
theorem witness_factorization :
    (∑ i, weights i*reported i)=radialResponse*directionWitness := by decide +kernel
/-- The complete, derived physical prediction error, in metres. -/
def physicalError : ℚ := data.positionError
/-- Exact lower bound in metres: the finite witness signal minus the
already certified physical prediction error. No allowance is introduced. -/
def lowerBound : ℚ := |∑ i, weights i*reported i|-physicalError

/-- Display rounding only: metres to millimetres (1000), then round down
to tenths of a millimetre (10). The primary theorem uses `lowerBound`. -/
def displayLower_mm : ℚ := (⌊(1000*10:ℚ)*lowerBound⌋:ℚ)/10
def displayLower_m : ℚ := displayLower_mm/1000
/-- The experiment's predeclared one-centimetre position target, converted
to metres. This is a requested accuracy, not a numerical error allowance. -/
def positionRequirement_m : ℚ := 1/100

theorem moments : ∀ k : Fin 4, ∑ i, weights i*nodes i^(k:ℕ)=0 := by decide +kernel
theorem variation : ∑ i, |weights i|=1 := by decide +kernel
/-- The derived display value is 11.7 millimetres. -/
theorem displayLower_value : displayLower_mm=117/10 := by decide +kernel
theorem displayLower_lt : displayLower_m<lowerBound := by decide +kernel
theorem requirement_below_lower : positionRequirement_m<lowerBound := by decide +kernel

noncomputable section

def inputs (i : Fin 5) : Fin 3 → ℝ := fun j => (points i j:ℝ)

theorem admissible (i : Fin 5) : Admissible (data.sigma:ℝ) (inputs i) := by
  change Admissible (((1/10:ℚ):ℝ)) (inputs i)
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  fin_cases i <;> norm_num [Admissible,inputs,points,a,b,Matrix.cons_val_two]

theorem moments_real : ∀ k ≤ 3, ∑ i, (weights i:ℝ)*(nodes i:ℝ)^k=0 := by
  intro k hk
  exact_mod_cast moments ⟨k,by omega⟩

theorem variation_real : ∑ i, |(weights i:ℝ)|=1 := by exact_mod_cast variation

theorem turn_inverse (t : ℝ) (z : E3) :
    HarmonicFrame.turn (-t) (HarmonicFrame.turn t z)=z := by
  ext i
  fin_cases i <;>
    simp [HarmonicFrame.turn,SpatialRotatingFrame.mix,pack_eq,mul_neg]
  · linear_combination z 0 * Real.sin_sq_add_cos_sq ((UniformCertificate.omega:ℝ)*t)
  · linear_combination z 1 * Real.sin_sq_add_cos_sq ((UniformCertificate.omega:ℝ)*t)

/-- Final reference RTN coordinates of a physical position deviation. -/
def framed (z : E3) : E3 :=
  HarmonicFrame.turn (-2) (z-PointingCapFrame.reference 2 1)

theorem candidate_frame (x : Fin 3 → ℝ) :
    framed (data.position x 1)=data.displacement x 1 := by
  change HarmonicFrame.turn (-2)
    ((PointingCapFrame.reference 2 1+HarmonicFrame.turn (2*1) (data.displacement x 1))-
       PointingCapFrame.reference 2 1)=_
  simp only [mul_one,add_sub_cancel_left,turn_inverse]

theorem frame_difference (z w : E3) : ‖framed z-framed w‖=‖z-w‖ := by
  simp only [framed,←map_sub,sub_sub_sub_cancel_right,HarmonicFrame.turn_norm]

theorem physical_sample (i : Fin 5)
    (X : Motion (data.alpha:ℝ) (direction (inputs i))) :
    |framed (X.p 1) 0-(reported i:ℝ)|≤(physicalError:ℝ) := by
  have hp := (data.certifies valid (admissible i) X 1 (by norm_num)).1
  have hn : ‖framed (X.p 1)-data.displacement (inputs i) 1‖≤(physicalError:ℝ) := by
    rw [←candidate_frame,frame_difference]
    simpa [physicalError] using hp
  have hc := (PiLp.norm_apply_le
    (framed (X.p 1)-data.displacement (inputs i) 1) 0).trans hn
  simp only [PiLp.sub_apply,Real.norm_eq_abs,Data.displacement,
    PointingCapPolynomial.vectorValue,pack_eq] at hc
  simpa only [reported,ParameterPolynomial.rationalValue_cast,Rat.cast_one,inputs] using hc

theorem coordinate_error_ge
    (X : ∀ i, Motion (data.alpha:ℝ) (direction (inputs i)))
    (p : Polynomial ℝ) (hp : p.natDegree≤3) :
    ∃ i, (lowerBound:ℝ) ≤ |framed ((X i).p 1) 0-p.eval (nodes i:ℝ)| := by
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 5 => |framed ((X i).p 1) 0-p.eval (nodes i:ℝ)|) (by simp)
  have hb := PolynomialObstruction.error_lower_bound
    (fun i => (nodes i:ℝ)) (fun i => (weights i:ℝ))
    (fun i => framed ((X i).p 1) 0) (fun i => (reported i:ℝ))
    (fun _ => (physicalError:ℝ)) moments_real variation_real
    (fun i => physical_sample i (X i)) p hp (fun j => hi j (by simp))
  have he : (∑ i, |(weights i:ℝ)| * (physicalError:ℝ))=(physicalError:ℝ) := by
    rw [←Finset.sum_mul,variation_real,one_mul]
  rw [he] at hb
  exact ⟨i,by simpa only [lowerBound,Rat.cast_sub,Rat.cast_abs,
    Rat.cast_sum,Rat.cast_mul] using hb⟩

theorem endpoint_error_ge
    (X : ∀ i, Motion (data.alpha:ℝ) (direction (inputs i)))
    (p : Fin 3 → Polynomial ℝ) (hp : (p 0).natDegree≤3) :
    ∃ i, (lowerBound:ℝ)≤
      ‖framed ((X i).p 1)-WithLp.toLp 2 (fun j => (p j).eval (nodes i:ℝ))‖ := by
  obtain ⟨i,hi⟩ := coordinate_error_ge X (p 0) hp
  have hc := PiLp.norm_apply_le
    (framed ((X i).p 1)-WithLp.toLp 2 (fun j : Fin 3 => (p j).eval (nodes i:ℝ))) (0:Fin 3)
  exact ⟨i,hi.trans (by simpa [PiLp.sub_apply,Real.norm_eq_abs] using hc)⟩

def physicalDeviation (i : Fin 5) : E3 :=
  framed ((data.trajectory valid (inputs i) (admissible i)).p 1)

/-- No physical trajectory/existence assumption remains: the certificate
constructs all five solutions and bounds the retained candidate over the cap. -/
theorem physical_comparison (p : Fin 3 → Polynomial ℝ) (hp : (p 0).natDegree≤3) :
    (∀ x, Admissible (data.sigma:ℝ) x →
      ∃ X : Motion (data.alpha:ℝ) (direction x), ∀ t ∈ Icc (0:ℝ) 1,
        ‖X.p t-data.position x t‖≤(physicalError:ℝ)) ∧
    ∃ i, (lowerBound:ℝ)≤
      ‖physicalDeviation i-WithLp.toLp 2 (fun j => (p j).eval (nodes i:ℝ))‖ := by
  constructor
  · intro x hx
    exact ⟨data.trajectory valid x hx,fun t ht =>
      (data.certifies valid hx (data.trajectory valid x hx) t ht).1⟩
  · exact endpoint_error_ge (fun i => data.trajectory valid (inputs i) (admissible i)) p hp

/-- Exact, data-derived obstruction for every bivariate polynomial of total
degree at most three. In particular, it applies to any fitted cubic, not
only the Taylor polynomial or a selected numerical implementation. -/
theorem transverse_error_ge (p : Fin 3 → MvPolynomial (Fin 2) ℝ)
    (hp : (p 0).totalDegree≤3) :
    ∃ i, Admissible (data.sigma:ℝ) (inputs i) ∧
      (lowerBound:ℝ)≤‖physicalDeviation i-
        WithLp.toLp 2 (fun j => MvPolynomial.eval ![(nodes i:ℝ),0] (p j))‖ := by
  have hd := (PolynomialSlice.firstAxis_degree (p 0)).trans hp
  obtain ⟨i,hi⟩ := (physical_comparison (fun j => PolynomialSlice.firstAxis (p j)) hd).2
  exact ⟨i,admissible i,by simpa only [PolynomialSlice.firstAxis_eval] using hi⟩

/-- Human-readable corollary, using the separately checked downward display
rounding. The value `displayLower_mm = 11.7` is in millimetres. -/
theorem transverse_display (p : Fin 3 → MvPolynomial (Fin 2) ℝ)
    (hp : (p 0).totalDegree≤3) :
    ∃ i, Admissible (data.sigma:ℝ) (inputs i) ∧
      (displayLower_m:ℝ)<‖physicalDeviation i-
        WithLp.toLp 2 (fun j => MvPolynomial.eval ![(nodes i:ℝ),0] (p j))‖ := by
  obtain ⟨i,ha,hi⟩ := transverse_error_ge p hp
  have h : (displayLower_m:ℝ)<(lowerBound:ℝ) := by exact_mod_cast displayLower_lt
  exact ⟨i,ha,h.trans_le hi⟩

/-- Meeting the declared one-centimetre requirement even at these five
physical directions requires a radial polynomial of degree at least four.
A uniform whole-cap accuracy guarantee in particular implies this premise. -/
theorem required_degree (p : Fin 3 → MvPolynomial (Fin 2) ℝ)
    (h : ∀ i, ‖physicalDeviation i-
      WithLp.toLp 2 (fun j => MvPolynomial.eval ![(nodes i:ℝ),0] (p j))‖≤
        (positionRequirement_m:ℝ)) :
    4≤(p 0).totalDegree := by
  by_contra hn
  obtain ⟨i,_,hi⟩ := transverse_error_ge p (by omega)
  have hl : (positionRequirement_m:ℝ)<(lowerBound:ℝ) := by
    exact_mod_cast requirement_below_lower
  exact hl.not_ge (hi.trans (h i))

end
end GNC.OrbitalComparison.PointingCapObstruction
