import GNC.Analysis.PolynomialAffine
import GNC.Analysis.PolynomialOrder
import GNC.Analysis.EuclideanBox
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Executable time-polynomial residuals for Cartesian first and quadratic
responses about a unit-radius reference. The polynomial reference need not
have exactly unit norm: these are polynomial surrogate operators, whose
discrepancy from the exact reference must be charged separately. Stored
coefficient proposals are checked against these actual operations.
-/
namespace GNC.CartesianResponsePolynomial
open Planning.PolynomialKernel Matrix
abbrev Vector := Fin 3 → List ℚ
noncomputable def value (p : Vector) (t : ℝ) : Vec3 := PolynomialAffine.value p t
def add (a b : Vector) : Vector := fun i => PolynomialBounds.add (a i) (b i)
def scale (a : ℚ) (p : Vector) : Vector := fun i => PolynomialBounds.scale a (p i)
def subtract (a b : Vector) : Vector := add a (scale (-1) b)
def multiply (a : List ℚ) (p : Vector) : Vector :=
  fun i => PolynomialBounds.multiply a (p i)
def pairing (a b : Vector) : List ℚ := PolynomialAffine.pairing a b
def derivative (p : Vector) : Vector := fun i => differentiate (p i)
def bound (p : Vector) : ℚ := ∑ i, PolynomialBounds.bound (p i) 1

theorem value_add (a b : Vector) (t : ℝ) : value (add a b) t=value a t+value b t := by
  ext i
  exact PolynomialOrder.value_add (a i) (b i) t

theorem value_scale (a : ℚ) (p : Vector) (t : ℝ) : value (scale a p) t=(a:ℝ) • value p t := by
  ext i
  exact PolynomialOrder.value_scale a (p i) t

theorem value_subtract (a b : Vector) (t : ℝ) :
    value (subtract a b) t=value a t-value b t := by
  rw [subtract,value_add,value_scale]
  simp [sub_eq_add_neg]

theorem scalar_multiply (a b : List ℚ) (t : ℝ) :
    PolynomialOrder.value (PolynomialBounds.multiply a b) t=
      PolynomialOrder.value a t*PolynomialOrder.value b t := by
  unfold PolynomialOrder.value
  rw [PolynomialBounds.multiply_map,PolynomialBounds.evaluate_multiply]

theorem value_multiply (a : List ℚ) (p : Vector) (t : ℝ) :
    value (multiply a p) t=PolynomialOrder.value a t • value p t := by
  ext i
  exact scalar_multiply a (p i) t

theorem value_pairing (a b : Vector) (t : ℝ) :
    PolynomialOrder.value (pairing a b) t=value a t ⬝ᵥ value b t :=
  PolynomialAffine.pairing_value a b t

theorem value_derivative (p : Vector) (t : ℝ) :
    HasDerivAt (value p) (value (derivative p) t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  exact PolynomialOrder.value_derivative (p i) t

theorem bound_nonnegative (p : Vector) : 0≤bound p := by
  apply Finset.sum_nonneg
  intro i _
  have h := PolynomialBounds.bound_sound (p i) (x := (0:ℝ)) (h := 1) (by norm_num)
  exact_mod_cast (abs_nonneg _).trans h

/-- An inexpensive Euclidean bound for a small coefficient residual. The
coefficient sum is a bound on every time, not a sampling assertion. -/
theorem value_bound (p : Vector) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    enorm (value p t)≤(bound p:ℝ) := by
  have hb (i : Fin 3) : |value p t i|≤(PolynomialBounds.bound (p i) 1:ℝ) :=
    PolynomialBounds.bound_sound (p i) (by simpa [abs_of_nonneg ht.1] using ht.2)
  have hn (i : Fin 3) : (0:ℝ)≤(PolynomialBounds.bound (p i) 1:ℝ) :=
    (abs_nonneg _).trans (hb i)
  apply enorm_le_of_component_bounds (value p t)
    (fun i => (PolynomialBounds.bound (p i) 1:ℝ)) hb
    (by exact_mod_cast bound_nonnegative p)
  simp only [bound,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Rat.cast_add]
  change (PolynomialBounds.bound (p 0) 1:ℝ)^2+
    ((PolynomialBounds.bound (p 1) 1:ℝ)^2+(PolynomialBounds.bound (p 2) 1:ℝ)^2)≤
    ((PolynomialBounds.bound (p 0) 1:ℝ)+
      ((PolynomialBounds.bound (p 1) 1:ℝ)+(PolynomialBounds.bound (p 2) 1:ℝ)))^2
  nlinarith [mul_nonneg (hn 0) (hn 1),mul_nonneg (hn 0) (hn 2),mul_nonneg (hn 1) (hn 2)]

def gradient (k : ℚ) (q y : Vector) : Vector :=
  scale k (subtract (scale 3 (multiply (pairing q y) q)) y)

/-- `c=1/2` gives a diagonal quadratic feature; `c=1` gives an unordered
off-diagonal feature, including both symmetric Hessian terms. -/
def hessian (k c : ℚ) (q y z : Vector) : Vector :=
  scale (3*k*c) (add (add (multiply (pairing q y) z) (multiply (pairing q z) y))
    (multiply (PolynomialBounds.subtract (pairing y z)
      (PolynomialBounds.scale 5 (PolynomialBounds.multiply (pairing q y) (pairing q z)))) q))

def linearResidual (k : ℚ) (q y force : Vector) : Vector :=
  subtract (derivative (derivative y)) (add (gradient k q y) force)

def quadraticResidual (k c : ℚ) (q y z response : Vector) : Vector :=
  subtract (derivative (derivative response))
    (add (gradient k q response) (hessian k c q y z))

theorem gradient_value (k : ℚ) (q y : Vector) (t : ℝ) :
    value (gradient k q y) t =
      (k:ℝ) • ((3*(value q t ⬝ᵥ value y t)) • value q t-value y t) := by
  simp only [gradient,value_scale,value_subtract,value_multiply,value_pairing,Rat.cast_ofNat,
    smul_smul]

theorem hessian_value (k c : ℚ) (q y z : Vector) (t : ℝ) :
    value (hessian k c q y z) t = (3*(k:ℝ)*(c:ℝ)) •
      ((value q t ⬝ᵥ value y t) • value z t+
       (value q t ⬝ᵥ value z t) • value y t+
       ((value y t ⬝ᵥ value z t)-5*(value q t ⬝ᵥ value y t)*(value q t ⬝ᵥ value z t)) • value q t) := by
  simp only [hessian,value_scale,value_add,value_multiply,value_pairing,
    PolynomialOrder.value_subtract,PolynomialOrder.value_scale,scalar_multiply,
    Rat.cast_mul,Rat.cast_ofNat]
  ring_nf

/-- A numerical predicate becomes a uniform bound for the actual stored
first-response coefficient curve and the polynomial surrogate operator. -/
theorem linear_bound (k : ℚ) (q y force : Vector) {B : ℚ}
    (hB : bound (linearResidual k q y force)≤B)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    enorm (value (derivative (derivative y)) t-
      ((k:ℝ) • ((3*(value q t ⬝ᵥ value y t)) • value q t-value y t)+value force t))≤(B:ℝ) := by
  have h := (value_bound (linearResidual k q y force) ht).trans
    (show (bound (linearResidual k q y force):ℝ)≤B by exact_mod_cast hB)
  simpa only [linearResidual,value_subtract,value_add,gradient_value] using h

theorem quadratic_bound (k c : ℚ) (q y z response : Vector) {B : ℚ}
    (hB : bound (quadraticResidual k c q y z response)≤B)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    enorm (value (derivative (derivative response)) t-
      (value (gradient k q response) t+value (hessian k c q y z) t))≤(B:ℝ) := by
  have h := (value_bound (quadraticResidual k c q y z response) ht).trans
    (show (bound (quadraticResidual k c q y z response):ℝ)≤B by exact_mod_cast hB)
  simpa only [quadraticResidual,value_subtract,value_add] using h

noncomputable def combination {n : ℕ} (p : Fin n → Vector)
    (w : Fin n → ℝ) (t : ℝ) : Vec3 := ∑ j, w j • value (p j) t

theorem enorm_sum_le {I : Type*} (s : Finset I) (v : I → Vec3) :
    enorm (∑ j ∈ s, v j)≤∑ j ∈ s, enorm (v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [enorm]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (enorm_add_le _ _).trans (add_le_add le_rfl ih)

/-- Uniform finite-feature enclosure. Rotation constraints can strengthen
this box bound, but are not needed to certify small coefficient residuals. -/
theorem combination_bound {n : ℕ} (p : Fin n → Vector) (w : Fin n → ℝ)
    (B : Fin n → ℚ) {r : ℚ} (hr : 0≤r)
    (hw : ∀ j, |w j|≤(r:ℝ)) (hB : ∀ j, bound (p j)≤B j)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    enorm (combination p w t)≤((r*∑ j, B j:ℚ):ℝ) := by
  have h (j : Fin n) : enorm (w j • value (p j) t)≤(r:ℝ)*(B j:ℝ) := by
    rw [enorm_smul]
    have hb := (value_bound (p j) ht).trans
      (show (bound (p j):ℝ)≤B j by exact_mod_cast hB j)
    exact mul_le_mul (hw j) hb (enorm_nonneg _) (by exact_mod_cast hr)
  calc
    _≤∑ j, enorm (w j • value (p j) t) := enorm_sum_le Finset.univ _
    _≤∑ j, (r:ℝ)*(B j:ℝ) := Finset.sum_le_sum (fun j _ => h j)
    _=_ := by simp [Finset.mul_sum]

theorem combination_derivative {n : ℕ} (p : Fin n → Vector)
    (w : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (combination p w)
      (combination (fun j => derivative (p j)) w t) t := by
  exact HasDerivAt.fun_sum (fun j _ => (value_derivative (p j) t).const_smul (w j))

end GNC.CartesianResponsePolynomial
