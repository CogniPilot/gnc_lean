import GNC.Applications.OrbitalComparison.FiniteEvaluationData
import GNC.Applications.OrbitalComparison.FiniteQueryGraphs

/-! A finite dyadic reference evaluator connected to both physical predictors.
The output is a rational grid value. This proves the mathematical evaluator,
not a compiler, CPU, bounded-word implementation or IEEE floating operation. -/
namespace GNC.OrbitalComparison.FiniteEvaluation
open ArithmeticProgram ArithmeticProgram.Rounding FiniteEvaluationData
open GeometricSTMPrediction (E)
open PoweredCircularLogTube (rate angleRadius lengthScale)
open Matrix
set_option maxRecDepth 4096
set_option maxHeartbeats 0

noncomputable def embed (v : Fin 3 → ℚ) : E := WithLp.toLp 2 (fun i => (v i:ℝ))
noncomputable def exactQuery {n : ℕ} (code : List (Instruction n)) (outputs : Fin 3 → ℕ)
    (input : Fin n → ℝ) : E := WithLp.toLp 2 (fun i => (values code input).getD (outputs i) 0)

def rationalQuery {n : ℕ} (code : List (Instruction n)) (outputs : Fin 3 → ℕ)
    (input : Fin n → ℚ) : Fin 3 → ℚ :=
  let values := roundedRatFrom grid input [] code
  fun i => values.getD (outputs i) 0

def phase (t : ℚ) : ℚ := dyadicRat grid (rateCenter*t)
def inputs (t : ℚ) (φ : Fin 3 → ℚ) : Fin 4 → ℚ :=
  ![phase t, dyadicRat grid (φ 0), dyadicRat grid (φ 1), dyadicRat grid (φ 2)]
noncomputable def angle (φ : Fin 3 → ℚ) : Vec3 := fun i => (φ i:ℝ)

def prediction (code : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (t : ℚ) (φ : Fin 3 → ℚ) : Fin 3 → ℚ :=
  let q := rationalQuery reference referenceOutputs (fun _ => phase t)
  let d := rationalQuery code outputs (inputs t φ)
  fun i => q i+d i

def physicalPrediction (code : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (t : ℚ) (φ : Fin 3 → ℚ) : Fin 3 → ℚ := fun i => 7000000*prediction code outputs t φ i

private theorem norm_le_abs_sum (v : E) : ‖v‖≤∑ i, |v i| := by
  have he : v=∑ i : Fin 3, (v i) • (PiLp.single 2 i (1:ℝ) : E) := by
    ext i
    simp [Pi.single_apply]
  calc
    ‖v‖ = ‖∑ i : Fin 3, (v i) • (PiLp.single 2 i (1:ℝ) : E)‖ := congrArg norm he
    _ ≤ ∑ i : Fin 3, ‖(v i) • (PiLp.single 2 i (1:ℝ) : E)‖ := norm_sum_le _ _
    _ = _ := by simp [norm_smul, PiLp.norm_single]

theorem query_error {n : ℕ} (input : Fin n → Budget) (x : Fin n → ℝ) (y : Fin n → ℚ)
    (hi : ∀ i, Holds (input i) (x i) (y i:ℝ))
    (code : List (Instruction n)) (outputs : Fin 3 → ℕ) :
    ‖embed (rationalQuery code outputs y)-exactQuery code outputs x‖≤
      (errorSum input code outputs:ℝ) := by
  calc
    _ ≤ ∑ i, |(embed (rationalQuery code outputs y)-exactQuery code outputs x) i| := norm_le_abs_sum _
    _ ≤ ∑ i, (((budgetsFrom roundingError input [] code).getD (outputs i) zero).error:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact rational_output_error grid_pos input x y hi code (outputs i)
    _ = _ := by simp only [errorSum, Rat.cast_sum]

theorem local_rounding (x : ℚ) : |(dyadicRat grid x:ℝ)-(x:ℝ)|≤(roundingError:ℝ) := by
  rw [dyadic_cast]
  simpa only [roundingError, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_one] using dyadic_error grid_pos (x:ℝ)

theorem rate_error : |rate-(rateCenter:ℝ)|≤(roundingError:ℝ) := by
  have hlo : (0:ℝ)≤(rateCenter:ℝ)-(roundingError:ℝ) := by exact_mod_cast rate_enclosure.1
  have hl : ((rateCenter:ℝ)-(roundingError:ℝ))^2≤(FiniteResponseData.speed2:ℝ) := by
    exact_mod_cast rate_enclosure.2.1
  have hu : (FiniteResponseData.speed2:ℝ)≤((rateCenter:ℝ)+(roundingError:ℝ))^2 := by
    exact_mod_cast rate_enclosure.2.2
  have hr : 0≤rate := Real.sqrt_nonneg _
  have hδ : (0:ℝ)≤(roundingError:ℝ) := by norm_num [roundingError, grid]
  apply abs_le.mpr
  constructor <;> nlinarith [FiniteCircularResponse.rate_squared]

theorem phase_error (t : ℚ) (ht : (t:ℝ)∈Set.Icc (0:ℝ) 1) :
    |(phase t:ℝ)-rate*(t:ℝ)|≤(2*roundingError:ℚ) := by
  have hq := local_rounding (rateCenter*t)
  have hr := rate_error
  have hs : |(rateCenter:ℝ)*(t:ℝ)-rate*(t:ℝ)|≤(roundingError:ℝ) := by
    rw [←sub_mul, abs_mul, abs_sub_comm, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right hr ht.1).trans
      (mul_le_of_le_one_right (by norm_num [roundingError, grid]) ht.2)
  have h := abs_sub_le (phase t:ℝ) ((rateCenter*t:ℚ):ℝ) (rate*(t:ℝ))
  simp only [Rat.cast_mul] at hq h
  change |(phase t:ℝ)-(rateCenter:ℝ)*(t:ℝ)|≤_ at hq
  norm_num only [Rat.cast_mul, Rat.cast_ofNat]
  linarith

theorem phase_holds (t : ℚ) (ht : (t:ℝ)∈Set.Icc (0:ℝ) 1) :
    Holds phaseBudget (rate*(t:ℝ)) (phase t:ℝ) := by
  refine ⟨FiniteResponseData.inputs.2.2.2.2.1, by norm_num [phaseBudget, roundingError, grid], ?_, phase_error t ht⟩
  change |rate*(t:ℝ)|≤(FiniteResponseData.horizon:ℝ)
  rw [abs_mul, abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_right FiniteCircularResponse.rate_bound ht.1).trans
    (mul_le_of_le_one_right (by exact_mod_cast FiniteResponseData.inputs.2.2.2.2.1) ht.2)

theorem input_holds (t : ℚ) (φ : Fin 3 → ℚ) (ht : (t:ℝ)∈Set.Icc (0:ℝ) 1)
    (hφ : enorm (angle φ)≤angleRadius) :
    ∀ i, Holds (inputBudget i) (FiniteQueryGraphs.input (rate*(t:ℝ)) (angle φ) i) (inputs t φ i:ℝ) := by
  have ha (i : Fin 3) : Holds angleBudget (φ i:ℝ) (dyadicRat grid (φ i):ℝ) := by
    refine ⟨by norm_num [angleBudget, FiniteResponseData.theta], by norm_num [angleBudget, roundingError, grid], ?_, local_rounding _⟩
    exact FiniteCircularResponse.feature_bound (angle φ) hφ i
  intro i
  fin_cases i <;> simp only [inputBudget, inputs, FiniteQueryGraphs.input, angle,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    first | exact phase_holds t ht | exact ha 0 | exact ha 1 | exact ha 2

theorem reference_correct (s : ℝ) :
    exactQuery reference referenceOutputs (fun _ => s)=FiniteCircularResponse.polynomialReference s := by
  ext i
  fin_cases i <;> norm_num [exactQuery, reference, referenceOutputs, values, runFrom, Instruction.eval,
    FiniteCircularResponse.polynomialReference, FiniteResponseData.c, FiniteResponseData.s,
    TrigonometricPolynomial.cosine, TrigonometricPolynomial.sine, PolynomialOrder.value,
    Planning.PolynomialKernel.evaluate, Matrix.cons_val_two] <;> ring <;> simp

theorem reference_error (t : ℚ) (ht : (t:ℝ)∈Set.Icc (0:ℝ) 1) :
    ‖embed (rationalQuery reference referenceOutputs (fun _ => phase t))-
      PoweredCircularLogTube.reference (t:ℝ)‖≤(referenceError+2*FiniteResponseData.delta:ℚ) := by
  have hr := query_error (fun _ : Fin 1 => phaseBudget) (fun _ => rate*(t:ℝ))
    (fun _ => phase t) (fun _ => phase_holds t ht) reference referenceOutputs
  rw [reference_correct] at hr
  have hp := FiniteCircularResponse.reference_error ht
  have hδ : (0:ℝ)≤(FiniteResponseData.delta:ℝ) := by exact_mod_cast FiniteResponseData.inputs.2.2.2.2.2.2.2
  have hp' : ‖FiniteCircularResponse.polynomialReference (rate*(t:ℝ))-
      PoweredCircularLogTube.reference (t:ℝ)‖≤2*(FiniteResponseData.delta:ℝ) := by
    rw [norm_sub_rev]
    exact hp.trans (mul_le_of_le_one_right (by positivity) (pow_le_one₀ ht.1 ht.2))
  have h := norm_sub_le_norm_sub_add_norm_sub (embed (rationalQuery reference referenceOutputs (fun _ => phase t)))
    (FiniteCircularResponse.polynomialReference (rate*(t:ℝ))) (PoweredCircularLogTube.reference (t:ℝ))
  simpa only [referenceError, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] using
    h.trans (add_le_add hr hp')

theorem prediction_error (code : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (t : ℚ) (φ : Fin 3 → ℚ) (ht : (t:ℝ)∈Set.Icc (0:ℝ) 1)
    (hφ : enorm (angle φ)≤angleRadius) :
    ‖embed (prediction code outputs t φ)-(PoweredCircularLogTube.reference (t:ℝ)+
      exactQuery code outputs (FiniteQueryGraphs.input (rate*(t:ℝ)) (angle φ)))‖≤
      (referenceError+errorSum inputBudget code outputs+2*FiniteResponseData.delta:ℚ) := by
  have hd := query_error inputBudget (FiniteQueryGraphs.input (rate*(t:ℝ)) (angle φ))
    (inputs t φ) (input_holds t φ ht hφ) code outputs
  have hr := reference_error t ht
  have he : embed (prediction code outputs t φ)-(PoweredCircularLogTube.reference (t:ℝ)+
      exactQuery code outputs (FiniteQueryGraphs.input (rate*(t:ℝ)) (angle φ)))=
    (embed (rationalQuery reference referenceOutputs (fun _ => phase t))-PoweredCircularLogTube.reference (t:ℝ))+
    (embed (rationalQuery code outputs (inputs t φ))-exactQuery code outputs (FiniteQueryGraphs.input (rate*(t:ℝ)) (angle φ))) := by
    ext i
    simp [embed, prediction, Rat.cast_add]
    ring
  rw [he]
  have h := (norm_add_le _ _).trans (add_le_add hr hd)
  simpa only [Rat.cast_add, add_assoc, add_comm, add_left_comm] using h

theorem physicalPrediction_embed (code : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (t : ℚ) (φ : Fin 3 → ℚ) :
    embed (physicalPrediction code outputs t φ)=lengthScale • embed (prediction code outputs t φ) := by
  ext i
  simp [embed, physicalPrediction, PoweredCircularLogTube.lengthScale]

theorem transfer (code : List (Instruction 4)) (outputs : Fin 3 → ℕ)
    (t : ℚ) (φ : Fin 3 → ℚ) (ht : (t:ℝ)∈Set.Icc (0:ℝ) 1)
    (hφ : enorm (angle φ)≤angleRadius) (x : E) (B : ℝ)
    (hcert : ‖x-(PoweredCircularLogTube.reference (t:ℝ)+
      exactQuery code outputs (FiniteQueryGraphs.input (rate*(t:ℝ)) (angle φ)))‖≤B) :
    ‖lengthScale • x-embed (physicalPrediction code outputs t φ)‖≤
      lengthScale*B+(7000000*(referenceError+errorSum inputBudget code outputs+2*FiniteResponseData.delta):ℚ) := by
  have hp := prediction_error code outputs t φ ht hφ
  rw [norm_sub_rev] at hp
  have h := norm_sub_le_norm_sub_add_norm_sub x (PoweredCircularLogTube.reference (t:ℝ)+
    exactQuery code outputs (FiniteQueryGraphs.input (rate*(t:ℝ)) (angle φ)))
    (embed (prediction code outputs t φ))
  have hn := h.trans (add_le_add hcert hp)
  rw [physicalPrediction_embed, ←smul_sub, norm_smul]
  have hL : (0:ℝ)≤lengthScale := by norm_num [PoweredCircularLogTube.lengthScale]
  rw [Real.norm_eq_abs, abs_of_nonneg hL]
  simpa only [mul_add, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, PoweredCircularLogTube.lengthScale] using
    mul_le_mul_of_nonneg_left hn hL

/-- Complete SI position certificates for executable rational queries on
53-fractional-bit normalized dyadics, including phase, reference and graph
rounding. The actual physical trajectory is still an explicit classical
solution hypothesis, and the statement is not about IEEE instructions. -/
theorem certificates (φ : Fin 3 → ℚ) (hφ : enorm (angle φ)≤angleRadius)
    (x xv : ℝ → E) (hx : Continuous x) (hxv : Continuous xv)
    (hdx : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt xv
      (Gravity.field PoweredCircularLogTube.μ (x t)+
        GeometricSTMPrediction.force (angle φ) (PoweredCircularLogTube.thrust t)) t)
    (hix : x 0=PoweredCircularLogTube.reference 0)
    (hixv : xv 0=PoweredCircularLogTube.referenceVelocity 0) :
    ∀ t : ℚ, (t:ℝ)∈Set.Icc (0:ℝ) 1 →
      ‖lengthScale • x (t:ℝ)-embed (physicalPrediction FiniteQueryGraphData.geometric
        FiniteQueryGraphData.geometricOutputs t φ)‖<913/1000000 ∧
      ‖lengthScale • x (t:ℝ)-embed (physicalPrediction FiniteQueryGraphData.cartesian
        FiniteQueryGraphData.cartesianOutputs t φ)‖<313/1000000 := by
  intro t ht
  have hg := FiniteCircularCertificate.certificate (angle φ) hφ x xv hx hxv hdx hdxv hix hixv (t:ℝ) ht
  have hc := FiniteCartesianCertificate.certificate .quadratic (angle φ) hφ x xv hx hxv hdx hdxv hix hixv (t:ℝ) ht
  constructor
  · have htG := transfer FiniteQueryGraphData.geometric FiniteQueryGraphData.geometricOutputs
      t φ ht hφ (x (t:ℝ)) _ (by
        simpa only [FiniteCircularCertificate.prediction, ←FiniteQueryGraphs.geometric_correct] using hg)
    have hb : (7000000:ℝ)*((FiniteResponseData.predictionBudget:ℝ)+
        (FiniteResponseData.reconstructionTail:ℝ)*(FiniteResponseData.responseRadius:ℝ))+
        (geometricNumerical:ℝ)<913/1000000 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr physical_budgets.1
      simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using h
    exact htG.trans_lt hb
  · have htC := transfer FiniteQueryGraphData.cartesian FiniteQueryGraphData.cartesianOutputs
      t φ ht hφ (x (t:ℝ)) _ (by
        simpa only [FiniteCartesianCertificate.prediction, ←FiniteQueryGraphs.cartesian_correct] using hc)
    have hb : (7000000:ℝ)*(FiniteCartesianData.predictionBudget .quadratic:ℝ)+
        (cartesianNumerical:ℝ)<313/1000000 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr physical_budgets.2
      simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using h
    exact htC.trans_lt hb

/-- A wholly rational admission check implies the domain used by `certificates`. -/
theorem domain_sufficient (t : ℚ) (φ : Fin 3 → ℚ) (ht0 : 0≤t) (ht1 : t≤1)
    (hφ : (φ 0)^2+(φ 1)^2+(φ 2)^2≤1/2500) :
    (t:ℝ)∈Set.Icc (0:ℝ) 1 ∧ enorm (angle φ)≤angleRadius := by
  refine ⟨⟨by exact_mod_cast ht0, by exact_mod_cast ht1⟩, ?_⟩
  have hs : ((φ 0:ℝ)^2+(φ 1:ℝ)^2+(φ 2:ℝ)^2)≤(1:ℝ)/2500 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hφ
    simpa only [Rat.cast_add, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have he := enorm_sq (angle φ)
  norm_num [angle, lengthSq] at he
  norm_num only [PoweredCircularLogTube.angleRadius]
  nlinarith [enorm_nonneg (angle φ)]

end GNC.OrbitalComparison.FiniteEvaluation
