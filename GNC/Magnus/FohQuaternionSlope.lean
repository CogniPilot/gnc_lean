import GNC.Magnus.FohSlopeVariation
import GNC.Magnus.FohCotangent
import Mathlib.Analysis.Quaternion

/-! Actual first and second slope variations in mean-axis quaternion coordinates. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology Quaternion
namespace GNC.Magnus

def fohQ (a b c d : ℝ) : ℍ := ⟨a, b, c, d⟩

theorem fohQ_derivative {a b c d : ℝ → ℝ} {da db dc dd t : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hc : HasDerivAt c dc t) (hd : HasDerivAt d dd t) :
    HasDerivAt (fun t => fohQ (a t) (b t) (c t) (d t)) (fohQ da db dc dd) t := by
  convert (((ha.smul_const (fohQ 1 0 0 0)).add
    (hb.smul_const (fohQ 0 1 0 0))).add
    ((hc.smul_const (fohQ 0 0 1 0)).add (hd.smul_const (fohQ 0 0 0 1)))) using 1 <;>
    ext <;> simp [fohQ]

def fohMeanQuaternion (θ t : ℝ) : ℍˣ where
  val := fohQ (Real.cos (θ * t / 2)) 0 0 (Real.sin (θ * t / 2))
  inv := fohQ (Real.cos (θ * t / 2)) 0 0 (-Real.sin (θ * t / 2))
  val_inv := by
    ext <;> simp [fohQ] <;> nlinarith [Real.sin_sq_add_cos_sq (θ * t / 2)]
  inv_val := by
    ext <;> simp [fohQ] <;> nlinarith [Real.sin_sq_add_cos_sq (θ * t / 2)]

@[simp] theorem fohMeanQuaternion_zero (θ : ℝ) : fohMeanQuaternion θ 0 = 1 := by
  apply Units.ext
  ext <;> simp [fohMeanQuaternion, fohQ]

theorem fohMeanQuaternion_derivative (θ t : ℝ) :
    HasDerivAt (fun t => (fohMeanQuaternion θ t).val)
      ((fohMeanQuaternion θ t).val * fohQ 0 0 0 (θ / 2)) t := by
  have hl : HasDerivAt (fun t : ℝ => θ * t / 2) (θ / 2) t := by
    convert ((hasDerivAt_id t).const_mul θ).div_const 2 using 1 <;> simp
  convert fohQ_derivative hl.cos (hasDerivAt_const t 0) (hasDerivAt_const t 0) hl.sin using 1
  ext <;> simp [fohMeanQuaternion, fohQ] <;> ring

def fohQuaternionSlopeInput (u v t : ℝ) : ℍ :=
  fohQ 0 ((t - 1 / 2) * u / 2) 0 ((t - 1 / 2) * v / 2)

theorem fohQuaternionSlopeInput_continuous (u v : ℝ) :
    Continuous (fohQuaternionSlopeInput u v) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (fohQ_derivative (hasDerivAt_const t 0)
    ((((hasDerivAt_id t).sub_const (1/2)).mul_const u).div_const 2)
    (hasDerivAt_const t 0)
    ((((hasDerivAt_id t).sub_const (1/2)).mul_const v).div_const 2)).continuousAt

/-- The right-flow interaction generator rotates the transverse slope with
positive angle. This fixes the chronological-product sign. -/
theorem fohQuaternionSlope_conjugated (θ u v t : ℝ) :
    fohConjugatedInput (fohMeanQuaternion θ) (fohQuaternionSlopeInput u v) t =
      fohQ 0 ((t - 1/2) * u * Real.cos (θ*t) / 2)
        ((t - 1/2) * u * Real.sin (θ*t) / 2) ((t - 1/2) * v / 2) := by
  have hcos := Real.cos_two_mul (θ*t/2)
  have hsin := Real.sin_two_mul (θ*t/2)
  have heq : 2 * (θ*t/2) = θ*t := by ring
  rw [heq] at hcos hsin
  have hs : Real.sin (θ*t/2)^2 = 1 - Real.cos (θ*t/2)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ*t/2)]
  ring_nf at hs
  ext <;> simp [fohConjugatedInput, fohMeanQuaternion, fohQuaternionSlopeInput, fohQ, hcos, hsin] <;>
    ring_nf <;> try simp only [hs] <;> ring

/-- Elementary primitives of the first interaction coefficient. -/
def fohSlopeCosPrimitive (θ t : ℝ) : ℝ :=
  (t-1/2) * Real.sin (θ*t) / θ + (Real.cos (θ*t)-1) / θ^2

def fohSlopeSinPrimitive (θ t : ℝ) : ℝ :=
  -(t-1/2) * Real.cos (θ*t) / θ + Real.sin (θ*t) / θ^2 - 1/(2*θ)

theorem fohSlopeCosPrimitive_derivative {θ : ℝ} (hθ : θ ≠ 0) (t : ℝ) :
    HasDerivAt (fohSlopeCosPrimitive θ) ((t-1/2)*Real.cos (θ*t)) t := by
  have hl := (hasDerivAt_id t).const_mul θ
  convert ((((hasDerivAt_id t).sub_const (1/2)).mul hl.sin).div_const θ).add
    ((hl.cos.sub_const 1).div_const (θ^2)) using 1
  dsimp
  field_simp
  <;> ring

theorem fohSlopeSinPrimitive_derivative {θ : ℝ} (hθ : θ ≠ 0) (t : ℝ) :
    HasDerivAt (fohSlopeSinPrimitive θ) ((t-1/2)*Real.sin (θ*t)) t := by
  have hl := (hasDerivAt_id t).const_mul θ
  convert (((((hasDerivAt_id t).sub_const (1/2)).neg.mul hl.cos).div_const θ).add
    (hl.sin.div_const (θ^2))).sub_const (1/(2*θ)) using 1
  dsimp
  field_simp
  <;> ring

def fohQuaternionInteractionFirst (θ u v t : ℝ) : ℍ :=
  fohQ 0 (u / 2 * fohSlopeCosPrimitive θ t)
    (u / 2 * fohSlopeSinPrimitive θ t) (v / 4 * (t^2-t))

theorem fohQuaternionInteractionFirst_derivative {θ : ℝ} (hθ : θ ≠ 0)
    (u v t : ℝ) :
    HasDerivAt (fohQuaternionInteractionFirst θ u v)
      (fohConjugatedInput (fohMeanQuaternion θ) (fohQuaternionSlopeInput u v) t) t := by
  rw [fohQuaternionSlope_conjugated]
  convert fohQ_derivative (hasDerivAt_const t 0)
    ((fohSlopeCosPrimitive_derivative hθ t).const_mul (u/2))
    ((fohSlopeSinPrimitive_derivative hθ t).const_mul (u/2))
    ((((hasDerivAt_id t).pow 2).sub (hasDerivAt_id t)).const_mul (v/4)) using 1
  ext <;> simp [fohQ] <;> ring

@[simp] theorem fohQuaternionInteractionFirst_zero {θ : ℝ} (hθ : θ ≠ 0) (u v : ℝ) :
    fohQuaternionInteractionFirst θ u v 0 = 0 := by
  ext <;> simp [fohQuaternionInteractionFirst, fohQ, fohSlopeCosPrimitive,
    fohSlopeSinPrimitive] <;> field_simp <;> ring <;> simp

theorem fohQuaternionInteractionFirst_integral {θ : ℝ} (hθ : θ ≠ 0) (u v T : ℝ) :
    (∫ t in (0 : ℝ)..T,
      fohConjugatedInput (fohMeanQuaternion θ) (fohQuaternionSlopeInput u v) t) =
      fohQuaternionInteractionFirst θ u v T := by
  have hc := foh_conjugatedInput_continuous (fohMeanQuaternion θ)
    (fun _ => fohQ 0 0 0 (θ/2)) (fohQuaternionSlopeInput u v)
    (fohMeanQuaternion_derivative θ) (fohQuaternionSlopeInput_continuous u v)
  simpa only [fohQuaternionInteractionFirst_zero hθ, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => fohQuaternionInteractionFirst_derivative hθ u v t)
      (hc.intervalIntegrable 0 T)

/-- The exact first Dyson endpoint is the cotangent first-slope coefficient. -/
theorem fohQuaternion_first_endpoint {θ : ℝ} (hθ : θ ≠ 0)
    (hs : Real.sin (θ/2) ≠ 0) (u v : ℝ) :
    fohSensitivityIntegral (fohMeanQuaternion θ) (fohQuaternionSlopeInput u v) 1 =
      fohQ 0 0 (u * Real.sin (θ/2) * fohCotC θ) 0 := by
  rw [fohSensitivityIntegral, fohQuaternionInteractionFirst_integral hθ]
  have hc : Real.cos θ = 2*Real.cos (θ/2)^2-1 := by
    convert Real.cos_two_mul (θ/2) using 1 <;> congr 1 <;> ring
  have hsn : Real.sin θ = 2*Real.sin (θ/2)*Real.cos (θ/2) := by
    convert Real.sin_two_mul (θ/2) using 1 <;> congr 1 <;> ring
  have hsq : Real.sin (θ/2)^2 = 1-Real.cos (θ/2)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  ring_nf at hsq
  ext <;> simp [fohQuaternionInteractionFirst, fohMeanQuaternion, fohQ,
    fohSlopeCosPrimitive, fohSlopeSinPrimitive, fohCotC, hc, hsn] <;>
    field_simp [hθ, hs] <;> ring_nf <;> try simp only [hsq] <;> ring

def fohQuaternionSecondPrimitive0 (θ t : ℝ) : ℝ :=
  ((1/16 : ℝ) * ((θ ^ 4):ℝ)⁻¹ * ((4 * Real.cos ((t * θ))) + ((θ ^ 2) * ((-2 * (t ^ 2)) + (2 * t) + (-2 * t * Real.cos ((t * θ))) + Real.cos ((t * θ)))) + (4 * t * θ * Real.sin ((t * θ)))))

theorem fohQuaternionSecondPrimitive0_derivative (θ t : ℝ) :
    HasDerivAt (fohQuaternionSecondPrimitive0 θ) (((1/16 : ℝ) * ((θ ^ 4):ℝ)⁻¹ * (((θ ^ 2) * (2 + (-4 * t) + (-2 * Real.cos ((t * θ))) + (-1 * θ * Real.sin ((t * θ))) + (2 * t * θ * Real.sin ((t * θ))))) + (4 * t * (θ ^ 2) * Real.cos ((t * θ)))))) t := by
  convert (((hasDerivAt_const t ((1/16 : ℝ) : ℝ)).mul (hasDerivAt_const t (((θ ^ 4):ℝ)⁻¹ : ℝ))).mul ((((hasDerivAt_const t (4 : ℝ)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos)).add ((hasDerivAt_const t ((θ ^ 2) : ℝ)).mul (((((hasDerivAt_const t (-2 : ℝ)).mul ((hasDerivAt_id t).pow 2)).add ((hasDerivAt_const t (2 : ℝ)).mul (hasDerivAt_id t))).add (((hasDerivAt_const t (-2 : ℝ)).mul (hasDerivAt_id t)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos))).add (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos)))).add ((((hasDerivAt_const t (4 : ℝ)).mul (hasDerivAt_id t)).mul (hasDerivAt_const t (θ : ℝ))).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin)))) using 1
  dsimp
  ring

def fohQuaternionSecondPrimitive1 (θ t : ℝ) : ℝ :=
  ((1/16 : ℝ) * ((θ ^ 4):ℝ)⁻¹ * ((24 * Real.sin ((t * θ))) + ((θ ^ 2) * ((-2 * Real.sin ((t * θ))) + (t * θ) + (-1 * θ * (t ^ 2)) + (-10 * (t ^ 2) * Real.sin ((t * θ))) + (10 * t * Real.sin ((t * θ))) + (t * θ * Real.cos ((t * θ))) + (-3 * θ * (t ^ 2) * Real.cos ((t * θ))) + (2 * θ * (t ^ 3) * Real.cos ((t * θ))))) + (12 * θ * (1 + (-2 * t)) * Real.cos ((t * θ)))))

theorem fohQuaternionSecondPrimitive1_derivative (θ t : ℝ) :
    HasDerivAt (fohQuaternionSecondPrimitive1 θ) (((1/16 : ℝ) * ((θ ^ 4):ℝ)⁻¹ * (((θ ^ 2) * (θ + (10 * Real.sin ((t * θ))) + (-1 * θ * Real.cos ((t * θ))) + (-20 * t * Real.sin ((t * θ))) + (-2 * t * θ) + (-1 * t * (θ ^ 2) * Real.sin ((t * θ))) + (-4 * θ * (t ^ 2) * Real.cos ((t * θ))) + (-2 * (t ^ 3) * (θ ^ 2) * Real.sin ((t * θ))) + (3 * (t ^ 2) * (θ ^ 2) * Real.sin ((t * θ))) + (4 * t * θ * Real.cos ((t * θ))))) + (-12 * (θ ^ 2) * (1 + (-2 * t)) * Real.sin ((t * θ)))))) t := by
  convert (((hasDerivAt_const t ((1/16 : ℝ) : ℝ)).mul (hasDerivAt_const t (((θ ^ 4):ℝ)⁻¹ : ℝ))).mul ((((hasDerivAt_const t (24 : ℝ)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin)).add ((hasDerivAt_const t ((θ ^ 2) : ℝ)).mul (((((((((hasDerivAt_const t (-2 : ℝ)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin)).add ((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ)))).add (((hasDerivAt_const t (-1 : ℝ)).mul (hasDerivAt_const t (θ : ℝ))).mul ((hasDerivAt_id t).pow 2))).add (((hasDerivAt_const t (-10 : ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin))).add (((hasDerivAt_const t (10 : ℝ)).mul (hasDerivAt_id t)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin))).add (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos))).add ((((hasDerivAt_const t (-3 : ℝ)).mul (hasDerivAt_const t (θ : ℝ))).mul ((hasDerivAt_id t).pow 2)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos))).add ((((hasDerivAt_const t (2 : ℝ)).mul (hasDerivAt_const t (θ : ℝ))).mul ((hasDerivAt_id t).pow 3)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos))))).add ((((hasDerivAt_const t (12 : ℝ)).mul (hasDerivAt_const t (θ : ℝ))).mul ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_const t (-2 : ℝ)).mul (hasDerivAt_id t)))).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos)))) using 1
  dsimp
  ring

def fohQuaternionSecondPrimitive2 (θ t : ℝ) : ℝ :=
  ((1/16 : ℝ) * ((θ ^ 4):ℝ)⁻¹ * ((-24 * Real.cos ((t * θ))) + ((θ ^ 2) * ((-2 * t) + (2 * (t ^ 2)) + (2 * Real.cos ((t * θ))) + (-10 * t * Real.cos ((t * θ))) + (10 * (t ^ 2) * Real.cos ((t * θ))) + (t * θ * Real.sin ((t * θ))) + (-3 * θ * (t ^ 2) * Real.sin ((t * θ))) + (2 * θ * (t ^ 3) * Real.sin ((t * θ))))) + (12 * θ * (1 + (-2 * t)) * Real.sin ((t * θ)))))

theorem fohQuaternionSecondPrimitive2_derivative (θ t : ℝ) :
    HasDerivAt (fohQuaternionSecondPrimitive2 θ) (((1/16 : ℝ) * ((θ ^ 4):ℝ)⁻¹ * (((θ ^ 2) * (-2 + (-10 * Real.cos ((t * θ))) + (4 * t) + (-1 * θ * Real.sin ((t * θ))) + (20 * t * Real.cos ((t * θ))) + (t * (θ ^ 2) * Real.cos ((t * θ))) + (-4 * θ * (t ^ 2) * Real.sin ((t * θ))) + (-3 * (t ^ 2) * (θ ^ 2) * Real.cos ((t * θ))) + (2 * (t ^ 3) * (θ ^ 2) * Real.cos ((t * θ))) + (4 * t * θ * Real.sin ((t * θ))))) + (12 * (θ ^ 2) * (1 + (-2 * t)) * Real.cos ((t * θ)))))) t := by
  convert (((hasDerivAt_const t ((1/16 : ℝ) : ℝ)).mul (hasDerivAt_const t (((θ ^ 4):ℝ)⁻¹ : ℝ))).mul ((((hasDerivAt_const t (-24 : ℝ)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos)).add ((hasDerivAt_const t ((θ ^ 2) : ℝ)).mul (((((((((hasDerivAt_const t (-2 : ℝ)).mul (hasDerivAt_id t)).add ((hasDerivAt_const t (2 : ℝ)).mul ((hasDerivAt_id t).pow 2))).add ((hasDerivAt_const t (2 : ℝ)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos))).add (((hasDerivAt_const t (-10 : ℝ)).mul (hasDerivAt_id t)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos))).add (((hasDerivAt_const t (10 : ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos))).add (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin))).add ((((hasDerivAt_const t (-3 : ℝ)).mul (hasDerivAt_const t (θ : ℝ))).mul ((hasDerivAt_id t).pow 2)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin))).add ((((hasDerivAt_const t (2 : ℝ)).mul (hasDerivAt_const t (θ : ℝ))).mul ((hasDerivAt_id t).pow 3)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin))))).add ((((hasDerivAt_const t (12 : ℝ)).mul (hasDerivAt_const t (θ : ℝ))).mul ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_const t (-2 : ℝ)).mul (hasDerivAt_id t)))).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin)))) using 1
  dsimp
  ring

def fohQuaternionSecondPrimitive3 (θ t : ℝ) : ℝ :=
  ((1/48 : ℝ) * ((θ ^ 4):ℝ)⁻¹ * ((-12 * Real.sin ((t * θ))) + ((θ ^ 2) * ((-3 * Real.sin ((t * θ))) + (-6 * θ * (t ^ 2)) + (3 * t * θ) + (4 * θ * (t ^ 3)) + (6 * t * Real.sin ((t * θ))))) + (12 * t * θ * Real.cos ((t * θ)))))

theorem fohQuaternionSecondPrimitive3_derivative (θ t : ℝ) :
    HasDerivAt (fohQuaternionSecondPrimitive3 θ) (((1/48 : ℝ) * ((θ ^ 4):ℝ)⁻¹ * (((θ ^ 2) * ((3 * θ) + (6 * Real.sin ((t * θ))) + (-12 * t * θ) + (-3 * θ * Real.cos ((t * θ))) + (12 * θ * (t ^ 2)) + (6 * t * θ * Real.cos ((t * θ))))) + (-12 * t * (θ ^ 2) * Real.sin ((t * θ)))))) t := by
  convert (((hasDerivAt_const t ((1/48 : ℝ) : ℝ)).mul (hasDerivAt_const t (((θ ^ 4):ℝ)⁻¹ : ℝ))).mul ((((hasDerivAt_const t (-12 : ℝ)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin)).add ((hasDerivAt_const t ((θ ^ 2) : ℝ)).mul ((((((hasDerivAt_const t (-3 : ℝ)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin)).add (((hasDerivAt_const t (-6 : ℝ)).mul (hasDerivAt_const t (θ : ℝ))).mul ((hasDerivAt_id t).pow 2))).add (((hasDerivAt_const t (3 : ℝ)).mul (hasDerivAt_id t)).mul (hasDerivAt_const t (θ : ℝ)))).add (((hasDerivAt_const t (4 : ℝ)).mul (hasDerivAt_const t (θ : ℝ))).mul ((hasDerivAt_id t).pow 3))).add (((hasDerivAt_const t (6 : ℝ)).mul (hasDerivAt_id t)).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).sin))))).add ((((hasDerivAt_const t (12 : ℝ)).mul (hasDerivAt_id t)).mul (hasDerivAt_const t (θ : ℝ))).mul (((hasDerivAt_id t).mul (hasDerivAt_const t (θ : ℝ))).cos)))) using 1
  dsimp
  ring

def fohQuaternionInteractionSecondPrimitive (θ u v t : ℝ) : ℍ :=
  fohQ (u^2 * fohQuaternionSecondPrimitive0 θ t - v^2 / 32 * (t^2-t)^2)
    (u*v * fohQuaternionSecondPrimitive1 θ t)
    (u*v * fohQuaternionSecondPrimitive2 θ t)
    (u^2 * fohQuaternionSecondPrimitive3 θ t)

/-- Differentiation of explicit elementary primitives verifies the second
ordered insertion, including its sign and its longitudinal cancellation. -/
theorem fohQuaternionInteractionSecondPrimitive_derivative {θ : ℝ} (hθ : θ ≠ 0)
    (u v t : ℝ) :
    HasDerivAt (fohQuaternionInteractionSecondPrimitive θ u v)
      (fohQuaternionInteractionFirst θ u v t *
        fohConjugatedInput (fohMeanQuaternion θ) (fohQuaternionSlopeInput u v) t) t := by
  rw [fohQuaternionSlope_conjugated]
  have hsq : Real.sin (θ*t)^2 = 1-Real.cos (θ*t)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ*t)]
  simp only [mul_comm θ t] at hsq
  ring_nf at hsq
  convert fohQ_derivative
    (((fohQuaternionSecondPrimitive0_derivative θ t).const_mul (u^2)).sub
      (((((hasDerivAt_id t).pow 2).sub (hasDerivAt_id t)).pow 2).const_mul (v^2/32)))
    ((fohQuaternionSecondPrimitive1_derivative θ t).const_mul (u*v))
    ((fohQuaternionSecondPrimitive2_derivative θ t).const_mul (u*v))
    ((fohQuaternionSecondPrimitive3_derivative θ t).const_mul (u^2)) using 1
  ext <;> simp [fohQuaternionInteractionFirst, fohQ,
    fohSlopeCosPrimitive, fohSlopeSinPrimitive, mul_comm θ t] <;>
    field_simp [hθ] <;> ring_nf <;> try simp only [hsq] <;> ring

theorem fohQuaternion_second_endpoint_integral {θ : ℝ} (hθ : θ ≠ 0) (u v : ℝ) :
    fohDysonSecond (fohMeanQuaternion θ) (fohQuaternionSlopeInput u v) 1 =
      (fohQuaternionInteractionSecondPrimitive θ u v 1 -
        fohQuaternionInteractionSecondPrimitive θ u v 0) * (fohMeanQuaternion θ 1).val := by
  rw [foh_dysonSecond_ordered_integral]
  simp_rw [fohQuaternionInteractionFirst_integral hθ]
  have hc1 : Continuous (fohQuaternionInteractionFirst θ u v) :=
    continuous_iff_continuousAt.mpr
      (fun t => (fohQuaternionInteractionFirst_derivative hθ u v t).continuousAt)
  have hc2 := foh_conjugatedInput_continuous (fohMeanQuaternion θ)
    (fun _ => fohQ 0 0 0 (θ/2)) (fohQuaternionSlopeInput u v)
    (fohMeanQuaternion_derivative θ) (fohQuaternionSlopeInput_continuous u v)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => fohQuaternionInteractionSecondPrimitive_derivative hθ u v t)
    ((hc1.mul hc2).intervalIntegrable 0 1)]

/-- Exact elementary quaternion coefficient at second slope order. -/
theorem fohQuaternion_second_endpoint {θ : ℝ} (hθ : θ ≠ 0) (u v : ℝ) :
    fohDysonSecond (fohMeanQuaternion θ) (fohQuaternionSlopeInput u v) 1 =
      fohQ
        (u^2 * (-(6*Real.cos (θ/2)*θ + θ^2*Real.sin (θ/2)-12*Real.sin (θ/2))/(48*θ^3)))
        (u*v * (-(6*Real.cos (θ/2)*θ + θ^2*Real.sin (θ/2)-12*Real.sin (θ/2))/(4*θ^4)))
        0
        (u^2 * ((Real.cos (θ/2)*θ^3+12*Real.cos (θ/2)*θ-24*Real.sin (θ/2))/(48*θ^4))) := by
  rw [fohQuaternion_second_endpoint_integral hθ]
  have hc : Real.cos θ = 2*Real.cos (θ/2)^2-1 := by
    convert Real.cos_two_mul (θ/2) using 1 <;> congr 1 <;> ring
  have hsn : Real.sin θ = 2*Real.sin (θ/2)*Real.cos (θ/2) := by
    convert Real.sin_two_mul (θ/2) using 1 <;> congr 1 <;> ring
  have hsq : Real.sin (θ/2)^2 = 1-Real.cos (θ/2)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  ring_nf at hsq
  ext <;> simp [fohQuaternionInteractionSecondPrimitive, fohMeanQuaternion, fohQ,
    fohQuaternionSecondPrimitive0, fohQuaternionSecondPrimitive1,
    fohQuaternionSecondPrimitive2, fohQuaternionSecondPrimitive3, hc, hsn] <;>
    field_simp [hθ] <;> ring_nf <;> try simp only [hsq] <;> ring

def fohQuaternionSlopeFirst (θ u : ℝ) : ℍ :=
  fohQ 0 0 (u * Real.sin (θ/2) * fohCotC θ) 0

def fohQuaternionSlopeSecond (θ u v : ℝ) : ℍ :=
  fohQ (u^2 * θ * Real.sin (θ/2) * fohCotD θ / 4)
    (u*v * Real.sin (θ/2) * fohCotBeta θ) 0
    (-u^2 * θ * Real.cos (θ/2) * fohCotD θ / 4 -
      u^2 * Real.sin (θ/2) * (fohCotC θ)^2 / 2)

/-- Exact second Dyson coefficient, now expressed in the cot coefficient
functions. This equality follows from the actual ordered integrals. -/
theorem fohQuaternion_second_endpoint_cot {θ : ℝ} (hθ : θ ≠ 0)
    (hs : Real.sin (θ/2) ≠ 0) (u v : ℝ) :
    fohDysonSecond (fohMeanQuaternion θ) (fohQuaternionSlopeInput u v) 1 =
      fohQuaternionSlopeSecond θ u v := by
  rw [fohQuaternion_second_endpoint hθ]
  have hsq : Real.sin (θ/2)^2 = 1-Real.cos (θ/2)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  ring_nf at hsq
  ext <;> simp [fohQuaternionSlopeSecond, fohQ, fohCotC, fohCotD, fohCotBeta] <;>
    field_simp [hθ, hs] <;> ring_nf <;> try simp only [hsq] <;> ring

/-- The unperturbed trajectory is forced by its time ODE and initial value;
it is not a separate premise on the parameter family. -/
theorem fohQuaternion_actual_base (θ u v : ℝ) (R : ℝ → ℝ → ℍˣ)
    (hR : ∀ e t, HasDerivAt (fun s => (R e s).val)
      ((R e t).val * (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t)
    (hR0 : ∀ e, R e 0 = 1) : R 0 = fohMeanQuaternion θ := by
  let F := fun t => (R 0 t).val * ((fohMeanQuaternion θ t)⁻¹).val
  have hd (t : ℝ) : HasDerivAt F 0 t := by
    have h := (hR 0 t).mul
      (foh_inverse_derivative (fohMeanQuaternion θ) (fun _ => fohQ 0 0 0 (θ/2))
        (fohMeanQuaternion_derivative θ) t)
    convert h using 1
    simp only [zero_smul, add_zero, mul_neg, neg_mul, mul_assoc, sub_self, add_neg_cancel]
  have he (t : ℝ) : F t = 1 := by
    have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa [F, hR0] using h
  funext t
  apply Units.ext
  have h := congrArg (fun q : ℍ => q * (fohMeanQuaternion θ t).val) (he t)
  simpa [F, mul_assoc] using h

/-- Actual centered affine quaternion flow has the cotangent first and
second coefficients and a cubic remainder. No parameter derivatives or
coefficient formulas are assumed. -/
theorem fohQuaternion_actual_cot_expansion {θ : ℝ} (hθ : θ ≠ 0)
    (hs : Real.sin (θ/2) ≠ 0) (u v : ℝ) (R : ℝ → ℝ → ℍˣ)
    (hR : ∀ e t, HasDerivAt (fun s => (R e s).val)
      ((R e t).val * (fohQ 0 0 0 (θ/2) + e • fohQuaternionSlopeInput u v t)) t)
    (hR0 : ∀ e, R e 0 = 1) :
    (fun e => (R e 1).val - (fohMeanQuaternion θ 1).val -
      e • fohQuaternionSlopeFirst θ u - e^2 • fohQuaternionSlopeSecond θ u v)
      =O[𝓝 0] (fun e : ℝ => e^3) := by
  have h := foh_actual_slope_cubic_isBigO (fun _ => fohQ 0 0 0 (θ/2))
    (fohQuaternionSlopeInput u v) R continuous_const
    (fohQuaternionSlopeInput_continuous u v) hR hR0 (by norm_num : (0 : ℝ) ≤ 1)
  rw [fohQuaternion_actual_base θ u v R hR hR0,
    fohQuaternion_first_endpoint hθ hs, fohQuaternion_second_endpoint_cot hθ hs] at h
  exact h

end GNC.Magnus
