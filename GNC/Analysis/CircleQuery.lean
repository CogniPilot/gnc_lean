import GNC.Analysis.CirclePolynomial

/-! Exact specialization of a retained-angle polynomial at a rational time.
Subtracting the same polynomial at zero angle preserves the shared nominal
before taking absolute coefficient bounds. The resulting bound covers every
real angle in the interval, not merely a finite set of queried angles. -/
namespace GNC.BivariatePolynomial
open Planning.PolynomialKernel

def atTime : Coefficients → ℚ → List ℚ
  | [], _ => []
  | cs :: p, t => PolynomialBounds.add cs (PolynomialBounds.scale t (atTime p t))

theorem row_atTime (p : Coefficients) (t : ℚ) (x : ℝ) :
    row (atTime p t) x = value p (t:ℝ) x := by
  induction p with
  | nil => simp [atTime,row,value,slice,evaluate]
  | cons cs p ih =>
    simp only [atTime,row_add,row_scale,ih,value,slice,List.map_cons,evaluate]

def zeroParameter (p : Coefficients) : Coefficients :=
  p.map (fun cs => [evaluate cs 0])

theorem row_atZero (cs : List ℚ) : row cs 0 = ((evaluate cs (0:ℚ):ℚ):ℝ) := by
  simpa [row] using evaluate_map (Rat.castHom ℝ) cs 0

theorem value_zeroParameter (p : Coefficients) (t x : ℝ) :
    value (zeroParameter p) t x = value p t 0 := by
  induction p with
  | nil => simp [zeroParameter,value,slice,evaluate]
  | cons cs p ih =>
    change row [evaluate cs 0] x+t*value (zeroParameter p) t x =
      row cs 0+t*value p t 0
    rw [ih,row_atZero]
    change (((evaluate cs (0:ℚ):ℚ):ℝ)+x*0)+t*value p t 0 =
      ((evaluate cs (0:ℚ):ℚ):ℝ)+t*value p t 0
    ring

end GNC.BivariatePolynomial

namespace GNC.CircleQuery
open CirclePolynomial Planning.PolynomialKernel

def atTime (p : Coefficients) (t : ℚ) : Coefficients :=
  ⟨[BivariatePolynomial.atTime p.even t], [BivariatePolynomial.atTime p.odd t]⟩

def zeroAngle (p : Coefficients) : Coefficients :=
  ⟨BivariatePolynomial.zeroParameter p.even, []⟩

theorem value_atTime (p : Coefficients) (t : ℚ) (s θ : ℝ) :
    value (atTime p t) s θ = value p (t:ℝ) θ := by
  change (BivariatePolynomial.row (BivariatePolynomial.atTime p.even t) (1-Real.cos θ)+s*0)+
    Real.sin θ*(BivariatePolynomial.row (BivariatePolynomial.atTime p.odd t) (1-Real.cos θ)+s*0) = _
  simp only [BivariatePolynomial.row_atTime,mul_zero,add_zero,value]

theorem value_zeroAngle (p : Coefficients) (t θ : ℝ) :
    value (zeroAngle p) t θ = value p t 0 := by
  change BivariatePolynomial.value (BivariatePolynomial.zeroParameter p.even) t (1-Real.cos θ)+
    Real.sin θ*BivariatePolynomial.value [] t (1-Real.cos θ) = _
  rw [BivariatePolynomial.value_zeroParameter]
  have hz : BivariatePolynomial.value [] t (1-Real.cos θ) = 0 := rfl
  rw [hz,mul_zero,add_zero]
  simp only [value,Real.cos_zero,sub_self,Real.sin_zero,zero_mul,add_zero]

def relative (p : Coefficients) (t : ℚ) : Coefficients :=
  atTime (subtract p (zeroAngle p)) t

theorem value_relative (p : Coefficients) (t : ℚ) (s θ : ℝ) :
    value (relative p t) s θ = value p (t:ℝ) θ-value p (t:ℝ) 0 := by
  rw [relative,value_atTime,value_subtract,value_zeroAngle]

def radius (p : Coefficients) (t a : ℚ) : ℚ := bound (relative p t) 1 a

/-- Exact rational range proposal, sound for a continuum of real angles. -/
theorem radius_sound (p : Coefficients) (t a : ℚ) {θ : ℝ} (hθ : |θ| ≤ (a:ℝ)) :
    |value p (t:ℝ) θ-value p (t:ℝ) 0| ≤ (radius p t a:ℝ) := by
  have h := bound_sound (relative p t) (t := 0) (h := 1) (by norm_num) hθ
  simpa only [value_relative,radius] using h

end GNC.CircleQuery
