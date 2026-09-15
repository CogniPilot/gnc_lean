import GNC.Applications.OrbitalComparison.VaryingRateReference
import GNC.Analysis.RotationPhaseCertificate
import GNC.Analysis.QuarticPointing
import GNC.Analysis.CirclePolynomial

/-! Exact forcing synthesis and phase-error budgets for the oblique inertial
attitude offset. All fractions come from the unit axis (0,-3/5,4/5).
Phase and pointing approximations are charged separately. -/
noncomputable section
set_option autoImplicit false
namespace GNC.OrbitalComparison.VaryingRateForcing
open SpatialBurn Real RotationPhaseCertificate
open scoped Matrix

@[simp] theorem phase_re (φ : ℝ) : (phase φ).re=cos φ := by simp [phase]
@[simp] theorem phase_im (φ : ℝ) : (phase φ).im=sin φ := by simp [phase]

def s0 (x y : ℝ) : E3 := pack (-(4/5)*y) ((4/5)*x) 0
def sCos (x : ℝ) : E3 := pack 0 0 ((3/5)*x)
def sSin (y : ℝ) : E3 := pack 0 0 (-(3/5)*y)
def c0 (x y : ℝ) : E3 := pack (-(41/50)*x) (-(41/50)*y) 0
def cCos1 (y : ℝ) : E3 := pack 0 0 (-(12/25)*y)
def cSin1 (x : ℝ) : E3 := pack 0 0 (-(12/25)*x)
def cCos2 (x y : ℝ) : E3 := pack (-(9/50)*x) ((9/50)*y) 0
def cSin2 (x y : ℝ) : E3 := pack ((9/50)*y) ((9/50)*x) 0

def first (p : ℂ) (x y : ℝ) : E3 := s0 x y+p.re • sCos x+p.im • sSin y
def second (p q : ℂ) (x y : ℝ) : E3 :=
  c0 x y+(p.re • cCos1 y+p.im • cSin1 x)+(q.re • cCos2 x y+q.im • cSin2 x y)
def source (θ φ x y : ℝ) : E3 :=
  sin θ • first (phase φ) x y+(1-cos θ) • second (phase φ) (phase (2*φ)) x y
def approximation (θ : ℝ) (p q : ℂ) (x y : ℝ) : E3 :=
  sin θ • first p x y+(1-cos θ) • second p q x y

theorem first_physical (φ x y : ℝ) :
    first (phase φ) x y=WithLp.toLp 2 (VaryingRateReference.firstForce φ x y) := by
  ext i
  fin_cases i <;> simp [first,s0,sCos,sSin,VaryingRateReference.firstForce,pack_eq] <;> ring

theorem second_physical (φ x y : ℝ) :
    second (phase φ) (phase (2*φ)) x y=WithLp.toLp 2 (VaryingRateReference.secondForce φ x y) := by
  ext i
  fin_cases i <;> simp [second,c0,cCos1,cSin1,cCos2,cSin2,
    VaryingRateReference.secondForce,pack_eq] <;> ring

theorem source_physical (θ φ x y : ℝ) : source θ φ x y=WithLp.toLp 2
    ((AxisRotation.zMatrix (-φ)*((attitude θ).val-1)*AxisRotation.zMatrix φ) *ᵥ ![x,y,0]) := by
  rw [VaryingRateReference.pointing_source]
  rw [source,first_physical,second_physical]
  rfl

private theorem s_pair_bound (x y : ℝ) : ‖sCos x‖+‖sSin y‖≤(3/5)*(|x|+|y|) := by
  have h := add_le_add (pack_norm_le 0 0 ((3/5)*x)) (pack_norm_le 0 0 (-(3/5)*y))
  norm_num [abs_mul] at h
  simpa only [sCos,sSin,neg_mul,mul_add] using h

private theorem c_pair1_bound (x y : ℝ) : ‖cCos1 y‖+‖cSin1 x‖≤(12/25)*(|x|+|y|) := by
  have h := add_le_add (pack_norm_le 0 0 (-(12/25)*y)) (pack_norm_le 0 0 (-(12/25)*x))
  norm_num [abs_mul] at h
  dsimp [cCos1,cSin1]
  simp only [neg_mul]
  linarith

private theorem c_pair2_bound (x y : ℝ) : ‖cCos2 x y‖+‖cSin2 x y‖≤(9/25)*(|x|+|y|) := by
  have h := add_le_add (pack_norm_le (-(9/50)*x) ((9/50)*y) 0)
    (pack_norm_le ((9/50)*y) ((9/50)*x) 0)
  norm_num [abs_mul] at h
  dsimp [cCos2,cSin2]
  simp only [neg_mul]
  linarith

theorem first_error (φ x y : ℝ) (p : ℂ) :
    ‖first p x y-first (phase φ) x y‖≤‖p-phase φ‖*((3/5)*(|x|+|y|)) := by
  have h := (synthesis_error (sCos x) (sSin y) p (phase φ)).trans
    (mul_le_mul_of_nonneg_left (s_pair_bound x y) (norm_nonneg _))
  convert h using 1
  congr 1
  dsimp [first]
  module

theorem second_error (φ x y : ℝ) (p q : ℂ) :
    ‖second p q x y-second (phase φ) (phase (2*φ)) x y‖≤
      ‖p-phase φ‖*((12/25)*(|x|+|y|))+‖q-phase (2*φ)‖*((9/25)*(|x|+|y|)) := by
  have h := (two_harmonic_error (cCos1 y) (cSin1 x) (cCos2 x y) (cSin2 x y) φ p q).trans
    (add_le_add (mul_le_mul_of_nonneg_left (c_pair1_bound x y) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (c_pair2_bound x y) (norm_nonneg _)))
  convert h using 1
  congr 1
  simp only [second,phase,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
  module

/-- The same phase budget used by the rational generator, for every angle
in the interval. No bound on angular rate is inserted into this estimate. -/
theorem approximation_error (θ φ x y : ℝ) (p q : ℂ) {σ L e1 e2 : ℝ}
    (hθ : |θ|≤σ) (hL : |x|+|y|≤L)
    (hp : ‖p-phase φ‖≤e1) (hq : ‖q-phase (2*φ)‖≤e2) :
    ‖approximation θ p q x y-source θ φ x y‖≤
      σ*((3/5)*L*e1)+(σ^2/2)*(L*((12/25)*e1+(9/25)*e2)) := by
  have hσ := (abs_nonneg θ).trans hθ
  have he1 := (norm_nonneg _).trans hp
  have he2 := (norm_nonneg _).trans hq
  have hLn := (add_nonneg (abs_nonneg x) (abs_nonneg y)).trans hL
  have hs : |sin θ|≤σ := abs_sin_le_abs.trans hθ
  have hc : |1-cos θ|≤σ^2/2 := by
    have hc := GNC.CirclePolynomial.cosine_bound θ
    have hsq : θ^2≤σ^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    linarith
  have hf : ‖first p x y-first (phase φ) x y‖≤(3/5)*L*e1 := by
    apply (first_error φ x y p).trans
    calc
      _ ≤ e1*((3/5)*L) := mul_le_mul hp (by linarith) (by positivity) he1
      _ = _ := by ring
  have hg : ‖second p q x y-second (phase φ) (phase (2*φ)) x y‖≤L*((12/25)*e1+(9/25)*e2) := by
    apply (second_error φ x y p q).trans
    have h1 := mul_le_mul hp (show (12/25:ℝ)*(|x|+|y|)≤(12/25)*L by linarith)
      (by positivity) he1
    have h2 := mul_le_mul hq (show (9/25:ℝ)*(|x|+|y|)≤(9/25)*L by linarith)
      (by positivity) he2
    nlinarith
  have he : approximation θ p q x y-source θ φ x y=
      sin θ • (first p x y-first (phase φ) x y)+
      (1-cos θ) • (second p q x y-second (phase φ) (phase (2*φ)) x y) := by
    dsimp [approximation,source]
    module
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs]
  exact add_le_add (mul_le_mul hs hf (norm_nonneg _) hσ)
    (mul_le_mul hc hg (norm_nonneg _) (by positivity))

private theorem synthesis_norm (a b : E3) (φ : ℝ) :
    ‖cos φ • a+sin φ • b‖≤‖a‖+‖b‖ := by
  simpa [phase_norm] using synthesis_error a b (phase φ) 0

theorem first_norm (φ x y : ℝ) : ‖first (phase φ) x y‖≤(7/5)*(|x|+|y|) := by
  have h0 := pack_norm_le (-(4/5)*y) ((4/5)*x) 0
  norm_num [abs_mul] at h0
  have h1 := (synthesis_norm (sCos x) (sSin y) φ).trans (s_pair_bound x y)
  have hn := norm_add_le (s0 x y) (cos φ • sCos x+sin φ • sSin y)
  have he : first (phase φ) x y=s0 x y+(cos φ • sCos x+sin φ • sSin y) := by
    simp [first,add_assoc]
  rw [he]
  dsimp [s0] at *
  simp only [neg_mul] at *
  linarith

theorem second_norm (φ x y : ℝ) :
    ‖second (phase φ) (phase (2*φ)) x y‖≤(83/50)*(|x|+|y|) := by
  have h0 := pack_norm_le (-(41/50)*x) (-(41/50)*y) 0
  norm_num [abs_mul] at h0
  have h1 := (synthesis_norm (cCos1 y) (cSin1 x) φ).trans (c_pair1_bound x y)
  have h2 := (synthesis_norm (cCos2 x y) (cSin2 x y) (2*φ)).trans (c_pair2_bound x y)
  have hn1 := norm_add_le (c0 x y) (cos φ • cCos1 y+sin φ • cSin1 x)
  have hn2 := norm_add_le (c0 x y+(cos φ • cCos1 y+sin φ • cSin1 x))
    (cos (2*φ) • cCos2 x y+sin (2*φ) • cSin2 x y)
  simp only [second,phase_re,phase_im]
  dsimp [c0] at *
  simp only [neg_mul] at *
  linarith

/-- A coarse physical forcing bound used only for existence. It is never
added to the much smaller prediction-error certificate. -/
theorem source_norm (θ φ x y : ℝ) {σ L : ℝ} (hθ : |θ|≤σ) (hL : |x|+|y|≤L) :
    ‖source θ φ x y‖≤((7/5)*σ+(83/100)*σ^2)*L := by
  have hσ := (abs_nonneg θ).trans hθ
  have hLn := (add_nonneg (abs_nonneg x) (abs_nonneg y)).trans hL
  have hs : |sin θ|≤σ := abs_sin_le_abs.trans hθ
  have hc : |1-cos θ|≤σ^2/2 := by
    have hc := CirclePolynomial.cosine_bound θ
    have hsq : θ^2≤σ^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    linarith
  have hf := (first_norm φ x y).trans (show (7/5:ℝ)*(|x|+|y|)≤(7/5)*L by linarith)
  have hg := (second_norm φ x y).trans (show (83/50:ℝ)*(|x|+|y|)≤(83/50)*L by linarith)
  have hn := norm_add_le (sin θ • first (phase φ) x y)
    ((1-cos θ) • second (phase φ) (phase (2*φ)) x y)
  simp only [norm_smul,Real.norm_eq_abs] at hn
  have h1 := mul_le_mul hs hf (norm_nonneg _) hσ
  have h2 := mul_le_mul hc hg (norm_nonneg _) (by positivity : 0≤σ^2/2)
  dsimp [source]
  nlinarith

end GNC.OrbitalComparison.VaryingRateForcing
