import GNC.Applications.OrbitalComparison.Envelopes
import GNC.Analysis.PolynomialOrder

/-! Polynomial-in-time error envelopes for the powered-orbit comparison.
The certificate retains the forcing time profile instead of replacing it by
its supremum before integration. Both predictors use the same checker.
-/
namespace GNC.OrbitalComparison.PolynomialEnvelope
open Planning.PolynomialKernel PolynomialOrder Set

def Valid (forcing envelope : List ℚ) : Prop :=
  nonnegative envelope ∧ nonnegative (differentiate envelope) ∧
  evaluate envelope 0 = 0 ∧ evaluate (differentiate envelope) 0 = 0 ∧
  prefixes 0 (PolynomialBounds.subtract (differentiate (differentiate envelope))
    (PolynomialBounds.add (PolynomialBounds.scale (17/20) envelope) forcing))

instance (f p : List ℚ) : Decidable (Valid f p) := by
  unfold Valid
  infer_instance

theorem supersolution (f p : List ℚ) (hp : Valid f p) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    (17/20:ℝ)*value p t+value f t ≤ value (differentiate (differentiate p)) t := by
  have h := prefixes_sound _ hp.2.2.2.2 ht
  simpa only [value_subtract,value_add,value_scale,Rat.cast_div,Rat.cast_ofNat,
    sub_nonneg] using h

/-- Every prefix, with zero initial error and no initial or forcing slack.
The auxiliary epsilon is eliminated by an order limit in the proof. -/
theorem response {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p v acc : ℝ → E) (f envelope : List ℚ) (henv : Valid f envelope)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (acc t) t)
    (hip : p 0 = 0) (hiv : v 0 = 0)
    (ha : ∀ t ∈ Icc (0:ℝ) 1, ‖acc t‖ ≤ (17/20)*‖p t‖+value f t) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖p t‖ ≤ ((evaluate envelope 1:ℚ):ℝ) ∧
      ‖v t‖ ≤ ((evaluate (differentiate envelope) 1:ℚ):ℝ) := by
  have hiP : value envelope 0 = 0 := by
    have h := value_at_rational envelope 0
    simpa only [Rat.cast_zero,henv.2.2.1] using h
  have hiV : value (differentiate envelope) 0 = 0 := by
    have h := value_at_rational (differentiate envelope) 0
    simpa only [Rat.cast_zero,henv.2.2.2.1] using h
  intro t ht
  have hb (ε : ℝ) (hε : 0 < ε) :
      ‖p t‖ ≤ value envelope 1+ε*(1+(17/20)*shape 1) ∧
      ‖v t‖ ≤ value (differentiate envelope) 1+ε*((17/20)*shapeV 1) := by
    have h := SecondOrderEnvelope.barrier p v acc
      (fun s => value envelope s+ε+((17/20)*ε)*shape s)
      (fun s => value (differentiate envelope) s+((17/20)*ε)*shapeV s)
      (fun s => value (differentiate (differentiate envelope)) s+((17/20)*ε)*shapeW s)
      hp hv hdp hdv
      (fun s => ((value_derivative envelope s).add_const ε).add
        ((shape_derivative s).const_mul ((17/20)*ε)))
      (fun s => (value_derivative (differentiate envelope) s).add
        ((shapeV_derivative s).const_mul ((17/20)*ε)))
      (by simpa only [hip,norm_zero,hiP,shape_initial.1,mul_zero,zero_add,add_zero] using hε)
      (by simp only [hiv,norm_zero,hiV,shape_initial.2,mul_zero,add_zero,le_refl]) (by
        intro s hs hreg
        have hdef := supersolution f envelope henv hs
        have hpert := mul_le_mul_of_nonneg_left (shape_defect hs)
          (show 0 ≤ (17/20:ℝ)*ε by positivity)
        have hacc := ha s hs
        nlinarith) t ht
    have hP := value_le_endpoint envelope henv.1 ht
    have hV := value_le_endpoint (differentiate envelope) henv.2.1 ht
    have hs := shape_bounds ht
    have hc : 0 ≤ (17/20:ℝ)*ε := by positivity
    have hsp := mul_le_mul_of_nonneg_left hs.2.1 hc
    have hsv := mul_le_mul_of_nonneg_left hs.2.2.2 hc
    constructor <;> nlinarith
  have hs := shape_bounds (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have h : ‖p t‖ ≤ value envelope 1 ∧ ‖v t‖ ≤ value (differentiate envelope) 1 :=
    ⟨remove_slack (by nlinarith [hs.1]) (fun ε hε => (hb ε hε).1),
      remove_slack (mul_nonneg (by norm_num) hs.2.2.1) (fun ε hε => (hb ε hε).2)⟩
  have hP := value_at_rational envelope 1
  have hV := value_at_rational (differentiate envelope) 1
  norm_num only [Rat.cast_one] at hP hV
  rwa [hP,hV] at h

end GNC.OrbitalComparison.PolynomialEnvelope
