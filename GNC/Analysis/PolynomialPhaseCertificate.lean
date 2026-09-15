import GNC.Analysis.RotationPhaseCertificate
import GNC.Analysis.BernsteinPolynomial

/-! A rational polynomial certificate for a prescribed, possibly varying,
angular rate. Bernstein bounds are checked for both components of the full
differential residual. The generator and its truncation order are untrusted.
The resulting phase error has no exponential factor in the angular rate.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.PolynomialPhaseCertificate
open PolynomialOrder Planning.PolynomialKernel Set

structure Data where
  rate : List ℚ
  cosine : List ℚ
  sine : List ℚ
  error : ℚ

def residualC (d : Data) : List ℚ :=
  PolynomialBounds.add (differentiate d.cosine) (PolynomialBounds.multiply d.rate d.sine)
def residualS (d : Data) : List ℚ :=
  PolynomialBounds.subtract (differentiate d.sine) (PolynomialBounds.multiply d.rate d.cosine)

def Valid (d : Data) : Prop :=
  d.cosine.headD 0=1 ∧ d.sine.headD 0=0 ∧ 0≤d.error ∧
  BernsteinPolynomial.checked (residualC d) 0 1 ^ 2+
    BernsteinPolynomial.checked (residualS d) 0 1 ^ 2≤d.error^2

instance (d : Data) : Decidable (Valid d) := by unfold Valid; infer_instance

def pair (c s : ℝ) : ℂ := (c:ℂ)+(s:ℂ)*Complex.I
def candidate (d : Data) (t : ℝ) : ℂ := pair (value d.cosine t) (value d.sine t)
def derivative (d : Data) (t : ℝ) : ℂ :=
  pair (value (differentiate d.cosine) t) (value (differentiate d.sine) t)

theorem pair_norm_sq (c s : ℝ) : ‖pair c s‖^2=c^2+s^2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,pair,pow_two]

theorem candidate_derivative (d : Data) (t : ℝ) :
    HasDerivAt (candidate d) (derivative d t) t :=
  (value_derivative d.cosine t).ofReal_comp.add
    ((value_derivative d.sine t).ofReal_comp.mul_const Complex.I)

theorem residual_identity (d : Data) (t : ℝ) :
    derivative d t-((value d.rate t:ℂ)*Complex.I)*candidate d t=
      pair (value (residualC d) t) (value (residualS d) t) := by
  have hm (p q : List ℚ) : value (PolynomialBounds.multiply p q) t=value p t*value q t := by
    unfold value
    rw [PolynomialBounds.multiply_map,PolynomialBounds.evaluate_multiply]
  simp only [residualC,residualS,value_add,value_subtract,hm,derivative,candidate,pair]
  apply Complex.ext <;> simp <;> ring

theorem residual_bound (d : Data) (hd : Valid d) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖derivative d t-((value d.rate t:ℂ)*Complex.I)*candidate d t‖≤(d.error:ℝ) := by
  have hc := BernsteinPolynomial.checked_sound (residualC d) (by norm_num : (0:ℚ)<1)
    (by simpa using ht)
  have hs := BernsteinPolynomial.checked_sound (residualS d) (by norm_num : (0:ℚ)<1)
    (by simpa using ht)
  have hb : (BernsteinPolynomial.checked (residualC d) 0 1:ℝ)^2+
      (BernsteinPolynomial.checked (residualS d) 0 1:ℝ)^2≤(d.error:ℝ)^2 := by
    exact_mod_cast hd.2.2.2
  have he : (0:ℝ)≤d.error := by exact_mod_cast hd.2.2.1
  have hc2 := sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hc) |>.mpr hc
  have hs2 := sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hs) |>.mpr hs
  rw [residual_identity]
  have hn := pair_norm_sq (value (residualC d) t) (value (residualS d) t)
  rw [sq_abs] at hc2 hs2
  nlinarith [norm_nonneg (pair (value (residualC d) t) (value (residualS d) t))]

/-- The numerical certificate includes its exact initial phase and every
coefficient of the oscillator residual, including omitted higher powers. -/
theorem certifies (d : Data) (hd : Valid d) (φ : ℝ → ℝ) (h0 : φ 0=0)
    (hφ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt φ (value d.rate t) t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖candidate d t-RotationPhaseCertificate.phase (φ t)‖≤(d.error:ℝ)*t := by
  apply RotationPhaseCertificate.error_bound φ (value d.rate) (candidate d) (derivative d)
    hφ (fun s _ => candidate_derivative d s) _ (fun s hs => residual_bound d hd hs) t ht
  have hv (p : List ℚ) : value p 0=(p.headD 0:ℝ) := by
    cases p <;> simp [value,evaluate]
  simp only [candidate,hv,hd.1,hd.2.1,h0]
  simp [RotationPhaseCertificate.phase,pair]

end GNC.PolynomialPhaseCertificate
