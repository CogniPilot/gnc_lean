import GNC.Analysis.TrigonometricPolynomial24
import GNC.Applications.OrbitalComparison.SpatialBurn
import GNC.Applications.OrbitalComparison.WeightedCertificate

/-! Verified trigonometric source polynomials for the three spatial burn laws.
The coefficient generator is not trusted. These source errors include both
the time and pointing Taylor remainders, including their product.
-/
namespace GNC.OrbitalComparison.SpatialSources
open UniformCertificate WeightedCertificate SpatialBurn Set
open Planning.PolynomialKernel

def timeEmbedding (a : ℚ) : List ℚ → BivariatePolynomial.Coefficients
  | [] => []
  | c::p => [c] :: BivariatePolynomial.scale a (timeEmbedding a p)

theorem timeEmbedding_value (a : ℚ) (p : List ℚ) (t θ : ℝ) :
    BivariatePolynomial.value (timeEmbedding a p) t θ = BivariatePolynomial.row p ((a:ℝ)*t) := by
  induction p with
  | nil => simp [timeEmbedding,BivariatePolynomial.value,BivariatePolynomial.slice,
      BivariatePolynomial.row,evaluate]
  | cons c p ih =>
    change BivariatePolynomial.row [c] θ+
      t*BivariatePolynomial.value (BivariatePolynomial.scale a (timeEmbedding a p)) t θ =
      (c:ℝ)+((a:ℝ)*t)*BivariatePolynomial.row p ((a:ℝ)*t)
    rw [BivariatePolynomial.value_scale,ih]
    simp only [BivariatePolynomial.row,List.map_cons,List.map_nil,evaluate,mul_zero,add_zero,Rat.coe_castHom]
    ring

def parameterError : ℚ := angle^25/15511210043330985984000000
def timeError : ℚ := omega^25/15511210043330985984000000

theorem parameter_bound {θ : ℝ} (hθ : |θ| ≤ (angle:ℝ)) :
    |θ|^25/15511210043330985984000000 ≤ (parameterError:ℝ) := by
  simp only [parameterError,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg θ) hθ 25) (by norm_num)

theorem time_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    |(omega:ℝ)*t|^25/15511210043330985984000000 ≤ (timeError:ℝ) := by
  have ho : (0:ℝ) ≤ omega := by norm_num [omega,Direct.angularSpeed]
  have hb : |(omega:ℝ)*t| ≤ (omega:ℝ) := by
    rw [abs_of_nonneg (mul_nonneg ho ht.1)]
    simpa using mul_le_mul_of_nonneg_left ht.2 ho
  simp only [timeError,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hb 25) (by norm_num)

noncomputable def polynomial24 : Representation BivariatePolynomial.Coefficients :=
  { polynomialRepresentation with
    sine := [TrigonometricPolynomial24.sine]
    cosineDifference := BivariatePolynomial.subtract [[1]] [TrigonometricPolynomial24.cosine]
    sourceError := parameterError
    sine_error := by
      intro t θ hθ
      change |Real.sin θ-BivariatePolynomial.value _ t θ| ≤ _
      have h := (TrigonometricPolynomial24.sine_bound θ).trans (parameter_bound hθ)
      simpa [BivariatePolynomial.value,BivariatePolynomial.slice,evaluate] using h
    cosine_error := by
      intro t θ hθ
      change |1-Real.cos θ-BivariatePolynomial.value _ t θ| ≤ _
      have h := (TrigonometricPolynomial24.cosine_bound θ).trans (parameter_bound hθ)
      rw [BivariatePolynomial.value_subtract]
      have he : BivariatePolynomial.value [[1]] t θ = 1 := by
        norm_num [BivariatePolynomial.value,BivariatePolynomial.slice,BivariatePolynomial.row,evaluate]
      have hc : BivariatePolynomial.value [TrigonometricPolynomial24.cosine] t θ =
          BivariatePolynomial.row TrigonometricPolynomial24.cosine θ := by
        simp [BivariatePolynomial.value,BivariatePolynomial.slice,evaluate]
      rw [he,hc,show 1-Real.cos θ-(1-BivariatePolynomial.row TrigonometricPolynomial24.cosine θ) =
        -(Real.cos θ-BivariatePolynomial.row TrigonometricPolynomial24.cosine θ) by ring,abs_neg]
      exact h }

noncomputable def polynomial24Time : TimeRepresentation polynomial24 where
  envelope := fun p => TimePolynomial.bivariate p angle
  nonnegative := fun p => TimePolynomial.bivariate_nonnegative p (by norm_num [angle])
  sound := fun p {_ _} ht hθ => TimePolynomial.bivariate_sound p ht hθ

structure Algebra (C : Type) where
  base : Representation C
  one : C
  value_one : ∀ t θ, base.value one t θ = 1
  cosTime : C
  sinTime : C
  cos_time_error : ∀ {t θ : ℝ}, t ∈ Icc (0:ℝ) 1 →
    |Real.cos ((omega:ℝ)*t)-base.value cosTime t θ| ≤ (timeError:ℝ)
  sin_time_error : ∀ {t θ : ℝ}, t ∈ Icc (0:ℝ) 1 →
    |Real.sin ((omega:ℝ)*t)-base.value sinTime t θ| ≤ (timeError:ℝ)

noncomputable def circle : Algebra CirclePolynomial.Coefficients where
  base := circleRepresentation
  one := ⟨[[1]],[]⟩
  value_one := by intros; norm_num [circleRepresentation,CirclePolynomial.value,
      BivariatePolynomial.value,BivariatePolynomial.slice,BivariatePolynomial.row,evaluate]
  cosTime := ⟨timeEmbedding omega TrigonometricPolynomial24.cosine,[]⟩
  sinTime := ⟨timeEmbedding omega TrigonometricPolynomial24.sine,[]⟩
  cos_time_error := by
    intro t θ ht
    change |Real.cos ((omega:ℝ)*t)-
      (BivariatePolynomial.value (timeEmbedding omega TrigonometricPolynomial24.cosine) t (1-Real.cos θ)+
        Real.sin θ*BivariatePolynomial.value [] t (1-Real.cos θ))| ≤ _
    rw [timeEmbedding_value]
    have h := (TrigonometricPolynomial24.cosine_bound ((omega:ℝ)*t)).trans (time_bound ht)
    simpa [circleRepresentation,CirclePolynomial.value,timeEmbedding_value,
      BivariatePolynomial.value,BivariatePolynomial.slice,evaluate] using h
  sin_time_error := by
    intro t θ ht
    change |Real.sin ((omega:ℝ)*t)-
      (BivariatePolynomial.value (timeEmbedding omega TrigonometricPolynomial24.sine) t (1-Real.cos θ)+
        Real.sin θ*BivariatePolynomial.value [] t (1-Real.cos θ))| ≤ _
    rw [timeEmbedding_value]
    have h := (TrigonometricPolynomial24.sine_bound ((omega:ℝ)*t)).trans (time_bound ht)
    simpa [circleRepresentation,CirclePolynomial.value,timeEmbedding_value,
      BivariatePolynomial.value,BivariatePolynomial.slice,evaluate] using h

noncomputable def ordinary : Algebra BivariatePolynomial.Coefficients where
  base := polynomial24
  one := [[1]]
  value_one := by intros; norm_num [polynomial24,polynomialRepresentation,
      BivariatePolynomial.value,BivariatePolynomial.slice,BivariatePolynomial.row,evaluate]
  cosTime := timeEmbedding omega TrigonometricPolynomial24.cosine
  sinTime := timeEmbedding omega TrigonometricPolynomial24.sine
  cos_time_error := by
    intro t θ ht
    change |Real.cos ((omega:ℝ)*t)-BivariatePolynomial.value _ t θ| ≤ _
    rw [timeEmbedding_value]
    exact (TrigonometricPolynomial24.cosine_bound ((omega:ℝ)*t)).trans (time_bound ht)
  sin_time_error := by
    intro t θ ht
    change |Real.sin ((omega:ℝ)*t)-BivariatePolynomial.value _ t θ| ≤ _
    rw [timeEmbedding_value]
    exact (TrigonometricPolynomial24.sine_bound ((omega:ℝ)*t)).trans (time_bound ht)

variable {C : Type} (A : Algebra C)

def cosine : C := A.base.add A.one (A.base.scale (-1) A.base.cosineDifference)

def polynomial (mode : Law) : Fin 3 → C :=
  let B := A.base
  let c := cosine A
  let s := B.sine
  let C := A.cosTime
  let S := A.sinTime
  match mode with
  | .rtnReferenceOffset =>
      ![B.add (B.multiply C c) (B.scale (-4/5) (B.multiply S s)),
        B.add (B.multiply S c) (B.scale (4/5) (B.multiply C s)), B.scale (3/5) s]
  | .rtnInertialOffset =>
      ![B.add (B.multiply C c) (B.scale (-4/5) (B.multiply S s)),
        B.add (B.add (B.scale (4/5) (B.multiply C s)) S)
          (B.scale (-16/25) (B.multiply S B.cosineDifference)),
        B.add (B.scale (3/5) (B.multiply C s))
          (B.scale (-12/25) (B.multiply S B.cosineDifference))]
  | .inertiallyFixed => ![c,B.scale (4/5) s,B.scale (3/5) s]

def sourceError (mode : Law) : ℚ :=
  let p := A.base.sourceError
  let product := timeError+p*(1+timeError)
  let difference := 2*timeError+p*(1+timeError)
  match mode with
  | .rtnReferenceOffset => (18/5)*product+(3/5)*p
  | .rtnInertialOffset => (16/5)*product+timeError+(28/25)*difference
  | .inertiallyFixed => (12/5)*p

theorem polynomial_value (mode : Law) (t θ : ℝ) (i : Fin 3) :
    A.base.value (polynomial A mode i) t θ =
      components mode (1-A.base.value A.base.cosineDifference t θ)
        (A.base.value A.base.sine t θ) (A.base.value A.cosTime t θ)
        (A.base.value A.sinTime t θ) i := by
  cases mode <;> fin_cases i <;>
    simp [polynomial,components,cosine,A.base.value_add,A.base.value_scale,
      A.base.value_multiply,A.value_one] <;> ring

/-- Includes the product of the two approximation errors. -/
theorem product_error {x y X Y dx dy B : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ B)
    (hex : |x-X| ≤ dx) (hey : |y-Y| ≤ dy) :
    |x*y-X*Y| ≤ B*dx+(1+dx)*dy := by
  have hdx : 0 ≤ dx := (abs_nonneg _).trans hex
  have hdy : 0 ≤ dy := (abs_nonneg _).trans hey
  have hB : 0 ≤ B := (abs_nonneg _).trans hy
  have hX : |X| ≤ 1+dx := by
    have h := abs_sub X x
    rw [abs_sub_comm X x] at h
    have he : X = x-(x-X) := by ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add hx hex)
  have he : x*y-X*Y = (x-X)*y+X*(y-Y) := by ring
  rw [he]
  have h := abs_add_le ((x-X)*y) (X*(y-Y))
  simp only [abs_mul] at h
  have h1 := mul_le_mul hex hy (abs_nonneg _) hdx
  have h2 := mul_le_mul hX hey (abs_nonneg _) (by positivity : 0 ≤ 1+dx)
  nlinarith

theorem component_errors (mode : Law) (c s C S cp sp Cp Sp p u e d : ℝ)
    (hc : |c-cp| ≤ p) (hs : |s-sp| ≤ p) (hS : |S-Sp| ≤ u)
    (hcc : |C*c-Cp*cp| ≤ e) (hss : |S*s-Sp*sp| ≤ e)
    (hsc : |S*c-Sp*cp| ≤ e) (hcs : |C*s-Cp*sp| ≤ e)
    (hd : |S*(1-c)-Sp*(1-cp)| ≤ d) :
    |components mode c s C S 0-components mode cp sp Cp Sp 0|+
    |components mode c s C S 1-components mode cp sp Cp Sp 1|+
    |components mode c s C S 2-components mode cp sp Cp Sp 2| ≤
      match mode with
      | .rtnReferenceOffset => (18/5)*e+(3/5)*p
      | .rtnInertialOffset => (16/5)*e+u+(28/25)*d
      | .inertiallyFixed => (12/5)*p := by
  have hcc' := abs_le.mp hcc
  have hss' := abs_le.mp hss
  have hsc' := abs_le.mp hsc
  have hcs' := abs_le.mp hcs
  have hd' := abs_le.mp hd
  have hc' := abs_le.mp hc
  have hs' := abs_le.mp hs
  have hS' := abs_le.mp hS
  have h0 : |C*c-(4/5)*S*s-(Cp*cp-(4/5)*Sp*sp)| ≤ (9/5)*e := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hcc'.1,hcc'.2,hss'.1,hss'.2]
  cases mode
  · have h1 : |S*c+(4/5)*C*s-(Sp*cp+(4/5)*Cp*sp)| ≤ (9/5)*e := by
      apply abs_le.mpr
      constructor <;> nlinarith only [hsc'.1,hsc'.2,hcs'.1,hcs'.2]
    have h2 : |(3/5)*s-(3/5)*sp| ≤ (3/5)*p := by
      apply abs_le.mpr
      constructor <;> nlinarith only [hs'.1,hs'.2]
    change _+_+_ ≤ (18/5)*e+(3/5)*p
    exact (add_le_add (add_le_add h0 h1) h2).trans_eq (by ring)
  · have h1 : |(4/5)*C*s+S-(16/25)*S*(1-c)-
        ((4/5)*Cp*sp+Sp-(16/25)*Sp*(1-cp))| ≤ (4/5)*e+u+(16/25)*d := by
      apply abs_le.mpr
      constructor <;> nlinarith only [hcs'.1,hcs'.2,hS'.1,hS'.2,hd'.1,hd'.2]
    have h2 : |(3/5)*C*s-(12/25)*S*(1-c)-
        ((3/5)*Cp*sp-(12/25)*Sp*(1-cp))| ≤ (3/5)*e+(12/25)*d := by
      apply abs_le.mpr
      constructor <;> nlinarith only [hcs'.1,hcs'.2,hd'.1,hd'.2]
    change _+_+_ ≤ (16/5)*e+u+(28/25)*d
    exact (add_le_add (add_le_add h0 h1) h2).trans_eq (by ring)
  · have h1 : |(4/5)*s-(4/5)*sp| ≤ (4/5)*p := by
      apply abs_le.mpr
      constructor <;> nlinarith only [hs'.1,hs'.2]
    have h2 : |(3/5)*s-(3/5)*sp| ≤ (3/5)*p := by
      apply abs_le.mpr
      constructor <;> nlinarith only [hs'.1,hs'.2]
    exact (add_le_add (add_le_add hc h1) h2).trans_eq (by ring)

noncomputable def approximation (mode : Law) (θ t : ℝ) : E3 :=
  pack (A.base.value (polynomial A mode 0) t θ) (A.base.value (polynomial A mode 1) t θ)
    (A.base.value (polynomial A mode 2) t θ)

/-- Uniform source error for actual SO(3) rotations, including the product
remainder when both the reference phase and pointing are approximated. -/
theorem approximation_error (mode : Law) {θ t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hθ : |θ| ≤ (angle:ℝ)) :
    ‖SpatialBurn.source mode θ t-approximation A mode θ t‖ ≤ (sourceError A mode:ℝ) := by
  let c := Real.cos θ
  let s := Real.sin θ
  let C := Real.cos ((omega:ℝ)*t)
  let S := Real.sin ((omega:ℝ)*t)
  let cp := 1-A.base.value A.base.cosineDifference t θ
  let sp := A.base.value A.base.sine t θ
  let Cp := A.base.value A.cosTime t θ
  let Sp := A.base.value A.sinTime t θ
  have hc : |c-cp| ≤ (A.base.sourceError:ℝ) := by
    have h := A.base.cosine_error t θ hθ
    dsimp [c,cp]
    rw [show Real.cos θ-(1-A.base.value A.base.cosineDifference t θ) =
      -(1-Real.cos θ-A.base.value A.base.cosineDifference t θ) by ring,abs_neg]
    exact h
  have hs : |s-sp| ≤ (A.base.sourceError:ℝ) := A.base.sine_error t θ hθ
  have hC : |C-Cp| ≤ (timeError:ℝ) := A.cos_time_error ht
  have hS : |S-Sp| ≤ (timeError:ℝ) := A.sin_time_error ht
  have hd : |(1-c)-(1-cp)| ≤ (A.base.sourceError:ℝ) := by
    simpa only [sub_sub_sub_cancel_left,abs_sub_comm] using hc
  have hdc : |1-c| ≤ 2 := by
    have h := Real.abs_cos_le_one θ
    have ha := abs_sub 1 c
    norm_num only [abs_one] at ha
    dsimp [c] at *
    linarith
  have hcc := product_error (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) hC hc
  have hss := product_error (Real.abs_sin_le_one _) (Real.abs_sin_le_one _) hS hs
  have hsc := product_error (Real.abs_sin_le_one _) (Real.abs_cos_le_one _) hS hc
  have hcs := product_error (Real.abs_cos_le_one _) (Real.abs_sin_le_one _) hC hs
  have hdc' := product_error (Real.abs_sin_le_one _) hdc hS hd
  let ep := (timeError:ℝ)+(A.base.sourceError:ℝ)*(1+timeError)
  let ed := 2*(timeError:ℝ)+(A.base.sourceError:ℝ)*(1+timeError)
  have hb := component_errors mode c s C S cp sp Cp Sp A.base.sourceError timeError ep ed
    hc hs hS (by convert hcc using 1 <;> dsimp [ep] <;> ring)
    (by convert hss using 1 <;> dsimp [ep] <;> ring)
    (by convert hsc using 1 <;> dsimp [ep] <;> ring)
    (by convert hcs using 1 <;> dsimp [ep] <;> ring)
    (by convert hdc' using 1 <;> dsimp [ed] <;> ring)
  have he : SpatialBurn.source mode θ t-approximation A mode θ t =
      pack (components mode c s C S 0-components mode cp sp Cp Sp 0)
        (components mode c s C S 1-components mode cp sp Cp Sp 1)
        (components mode c s C S 2-components mode cp sp Cp Sp 2) := by
    rw [SpatialBurn.source_components]
    simp only [approximation,polynomial_value]
    dsimp [c,s,C,S,cp,sp,Cp,Sp,pack]
    module
  rw [he]
  apply (pack_norm_le _ _ _).trans
  convert hb using 1
  cases mode <;> simp only [sourceError] <;> push_cast <;> dsimp [ep,ed] <;> ring

end GNC.OrbitalComparison.SpatialSources
