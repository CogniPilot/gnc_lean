import GNC.Analysis.SphereResponse
import GNC.Analysis.BernsteinPolynomial
import GNC.Analysis.BernsteinSubdivision

/-! An algebraic source-error certificate for a forward pointing cap.
Checking a polynomial's unit-length residual replaces a square-root series
tail. The branch and denominator are explicit geometric conditions. -/
namespace GNC.RadialSourceCertificate

def residual (p : List ℚ) : List ℚ := PolynomialBounds.add [0,1]
  (PolynomialBounds.subtract (PolynomialBounds.multiply p p) (PolynomialBounds.scale 2 p))

theorem residual_value (p : List ℚ) (s : ℝ) :
    PolynomialOrder.value (residual p) s=
      s-2*PolynomialOrder.value p s+(PolynomialOrder.value p s)^2 := by
  rw [residual,PolynomialOrder.value_add,PolynomialOrder.value_subtract,
    PolynomialOrder.value_scale]
  simp only [PolynomialOrder.value,PolynomialBounds.multiply_map,
    PolynomialBounds.evaluate_multiply,Planning.PolynomialKernel.evaluate]
  norm_num only [List.map_cons,List.map_nil,Rat.coe_castHom,Rat.cast_zero,Rat.cast_one,
    Rat.cast_ofNat,Planning.PolynomialKernel.evaluate]
  ring

theorem constraint_error {s c a C U B : ℝ} (hc : c^2-2*c+s=0)
    (hC : c≤C) (hU : a≤U) (hgap : 0<2-C-U)
    (hres : |s-2*a+a^2|≤B) : |c-a|≤B/(2-C-U) := by
  have hd : 0<2-c-a := by linarith
  have he : (c-a)*(2-c-a)=s-2*a+a^2 := by nlinarith
  have hm : |c-a| * (2-c-a)≤B := by
    simpa only [← he,abs_mul,abs_of_pos hd] using hres
  apply (le_div_iff₀ hgap).2
  exact (mul_le_mul_of_nonneg_left (by linarith : 2-C-U≤2-c-a) (abs_nonneg _)).trans hm

def capDepth (h : ℚ) : ℚ := h/(2-h)
def sourceBound (p : List ℚ) (h : ℚ) : ℚ := BernsteinPolynomial.checked p 0 h
def errorBound (p : List ℚ) (h : ℚ) : ℚ :=
  BernsteinPolynomial.checked (residual p) 0 h/(2-capDepth h-sourceBound p h)

def Valid (p : List ℚ) (h : ℚ) : Prop :=
  0<h ∧ h<1 ∧ 0<2-capDepth h-sourceBound p h
instance (p : List ℚ) (h : ℚ) : Decidable (Valid p h) := by unfold Valid; infer_instance

/-- Uniform over both transverse directions, without choosing an angle
axis. The complete source discrepancy is checked by an exact polynomial
residual and the forward branch, rather than a truncation-order assumption. -/
theorem certifies (p : List ℚ) (h : ℚ) (hv : Valid p h) (u v c : ℝ)
    (hc0 : 0≤c) (hc1 : c≤1) (hs : u^2+v^2=2*c-c^2)
    (hcap : u^2+v^2≤(h:ℝ)) :
    |c-PolynomialOrder.value p (u^2+v^2)|≤(errorBound p h:ℝ) := by
  have ht : u^2+v^2 ∈ Set.Icc ((0:ℚ):ℝ) (h:ℝ) :=
    ⟨by norm_num only [Rat.cast_zero]; positivity,hcap⟩
  have hp := BernsteinPolynomial.checked_sound p hv.1 ht
  have hr := BernsteinPolynomial.checked_sound (residual p) hv.1 ht
  rw [residual_value] at hr
  have hC := SphereResponse.cap_depth_bound hc0 hc1 (show (h:ℝ)<1 by exact_mod_cast hv.2.1) hs hcap
  have hgap : 0<2-(capDepth h:ℝ)-(sourceBound p h:ℝ) := by exact_mod_cast hv.2.2
  have hb := constraint_error (by nlinarith : c^2-2*c+(u^2+v^2)=0)
    (show c≤(capDepth h:ℝ) by simpa [capDepth] using hC)
    ((le_abs_self _).trans hp) hgap hr
  simpa only [errorBound,sourceBound,Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat] using hb

def refinedError (depth : ℕ) (p : List ℚ) (h : ℚ) : ℚ :=
  BernsteinSubdivision.bound depth (residual p) 0 h/(2-capDepth h-sourceBound p h)

/-- Finite interval refinement improves the scalar residual enclosure. The
work depth is explicit, and no iteration of an unknown orbital tube occurs. -/
theorem refined_certifies (depth : ℕ) (p : List ℚ) (h : ℚ) (hv : Valid p h) (u v c : ℝ)
    (hc0 : 0≤c) (hc1 : c≤1) (hs : u^2+v^2=2*c-c^2)
    (hcap : u^2+v^2≤(h:ℝ)) :
    |c-PolynomialOrder.value p (u^2+v^2)|≤(refinedError depth p h:ℝ) := by
  have ht : u^2+v^2 ∈ Set.Icc ((0:ℚ):ℝ) (h:ℝ) :=
    ⟨by norm_num only [Rat.cast_zero]; positivity,hcap⟩
  have hp := BernsteinPolynomial.checked_sound p hv.1 ht
  have hr := BernsteinSubdivision.sound depth (residual p) hv.1 ht
  rw [residual_value] at hr
  have hC := SphereResponse.cap_depth_bound hc0 hc1 (show (h:ℝ)<1 by exact_mod_cast hv.2.1) hs hcap
  have hgap : 0<2-(capDepth h:ℝ)-(sourceBound p h:ℝ) := by exact_mod_cast hv.2.2
  have hb := constraint_error (by nlinarith : c^2-2*c+(u^2+v^2)=0)
    (show c≤(capDepth h:ℝ) by simpa [capDepth] using hC)
    ((le_abs_self _).trans hp) hgap hr
  simpa only [refinedError,sourceBound,Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat] using hb

theorem refined_no_worse (depth : ℕ) (p : List ℚ) (h : ℚ) (hv : Valid p h) :
    refinedError depth p h≤errorBound p h :=
  div_le_div_of_nonneg_right (BernsteinSubdivision.no_worse depth (residual p) 0 h) hv.2.2.le

end GNC.RadialSourceCertificate
