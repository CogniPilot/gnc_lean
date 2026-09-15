import GNC.Analysis.BernsteinPolynomial

/-! Sparse parameter polynomials with univariate time coefficients. This
executable front end reuses GNC's checked univariate arithmetic and mathlib's
Bernstein range theorem. Sparse identities, differentiation and whole-domain
bounds are verified; an external coefficient generator need not be trusted. -/
namespace GNC.ParameterPolynomial
open Planning.PolynomialKernel

structure Term where
  u : ℕ
  v : ℕ
  c : ℕ
  time : List ℚ
 deriving DecidableEq, Repr

abbrev Coefficients := List Term

noncomputable def monomial (a : Term) (x : Fin 3 → ℝ) : ℝ := x 0^a.u*x 1^a.v*x 2^a.c
noncomputable def termValue (a : Term) (x : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  PolynomialOrder.value a.time t*monomial a x
noncomputable def value (p : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  (p.map fun a => termValue a x t).sum

@[simp] theorem value_nil (x : Fin 3 → ℝ) (t : ℝ) : value [] x t=0 := rfl
@[simp] theorem value_cons (a : Term) (p : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value (a::p) x t=termValue a x t+value p x t := rfl

def insert (a : Term) : Coefficients → Coefficients
  | [] => [a]
  | b::p => if a.u=b.u ∧ a.v=b.v ∧ a.c=b.c then
      {b with time := PolynomialBounds.add a.time b.time}::p
    else b::insert a p

def add : Coefficients → Coefficients → Coefficients
  | [],q => q
  | a::p,q => insert a (add p q)

def scale (r : ℚ) (p : Coefficients) : Coefficients :=
  p.map fun a => {a with time := PolynomialBounds.scale r a.time}

def subtract (p q : Coefficients) : Coefficients := add p (scale (-1) q)

def termMultiply (a b : Term) : Term :=
  ⟨a.u+b.u,a.v+b.v,a.c+b.c,PolynomialBounds.multiply a.time b.time⟩

def multiply : Coefficients → Coefficients → Coefficients
  | [],_ => []
  | a::p,q => add (q.map (termMultiply a)) (multiply p q)

def derivative (p : Coefficients) : Coefficients :=
  p.map fun a => {a with time := differentiate a.time}

def constant (r : ℚ) : Coefficients := [⟨0,0,0,[r]⟩]

def zero (p : Coefficients) : Prop := ∀ a ∈ p, BernsteinPolynomial.zero a.time
instance (p : Coefficients) : Decidable (zero p) := by unfold zero; infer_instance

theorem value_insert (a : Term) (p : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value (insert a p) x t=termValue a x t+value p x t := by
  induction p with
  | nil => simp [insert]
  | cons b p ih =>
    simp only [insert]
    split_ifs with h
    · simp only [value_cons,termValue,PolynomialOrder.value_add,monomial]
      rw [h.1,h.2.1,h.2.2]
      ring
    · simp only [value_cons,ih]
      ring

theorem value_add (p q : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value (add p q) x t=value p x t+value q x t := by
  induction p with
  | nil => simp [add]
  | cons a p ih => simp only [add,value_insert,ih,value_cons]; ring

theorem value_scale (r : ℚ) (p : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value (scale r p) x t=(r:ℝ)*value p x t := by
  induction p with
  | nil => simp [scale]
  | cons a p ih =>
    simp only [scale,List.map_cons,value_cons] at *
    rw [ih]
    simp only [termValue,monomial,PolynomialOrder.value_scale]
    ring

theorem value_subtract (p q : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value (subtract p q) x t=value p x t-value q x t := by
  simp [subtract,value_add,value_scale,sub_eq_add_neg]

theorem value_termMultiply (a b : Term) (x : Fin 3 → ℝ) (t : ℝ) :
    termValue (termMultiply a b) x t=termValue a x t*termValue b x t := by
  simp only [termValue,termMultiply,monomial,PolynomialOrder.value,
    PolynomialBounds.multiply_map,PolynomialBounds.evaluate_multiply,pow_add]
  ring

theorem value_multiply (p q : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value (multiply p q) x t=value p x t*value q x t := by
  have hm (a : Term) : value (q.map (termMultiply a)) x t=termValue a x t*value q x t := by
    induction q with
    | nil => simp
    | cons b q ih => simp only [List.map_cons,value_cons,value_termMultiply,ih]; ring
  induction p with
  | nil => simp [multiply]
  | cons a p ih => simp only [multiply,value_add,hm,ih,value_cons]; ring

theorem value_derivative (p : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (value p x) (value (derivative p) x t) t := by
  induction p with
  | nil => simpa [derivative] using hasDerivAt_const t (0:ℝ)
  | cons a p ih =>
    have ha := (PolynomialOrder.value_derivative a.time t).mul_const (monomial a x)
    simpa only [derivative,List.map_cons,value_cons,termValue,monomial] using ha.add ih

theorem value_constant (r : ℚ) (x : Fin 3 → ℝ) (t : ℝ) :
    value (constant r) x t=(r:ℝ) := by
  simp [constant,value,termValue,monomial,PolynomialOrder.value,evaluate]

theorem value_zero (p : Coefficients) (hp : zero p) (x : Fin 3 → ℝ) (t : ℝ) :
    value p x t=0 := by
  have hz (cs : List ℚ) (hc : BernsteinPolynomial.zero cs) : PolynomialOrder.value cs t=0 := by
    induction cs with
    | nil => rfl
    | cons a cs ih =>
      have ha := hc a (by simp)
      have hb := ih (fun b hb => hc b (by simp [hb]))
      change (a:ℝ)+t*PolynomialOrder.value cs t=0
      simp [ha,hb]
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [value_cons,ih (fun b hb => hp b (by simp [hb]))]
    simp [termValue,hz a.time (hp a (by simp))]

theorem identity (p q : Coefficients) (h : zero (subtract p q)) (x : Fin 3 → ℝ) (t : ℝ) :
    value p x t=value q x t := by
  have he := value_zero _ h x t
  rw [value_subtract] at he
  exact sub_eq_zero.mp he

def bound (p : Coefficients) (r : Fin 3 → ℚ) : ℚ :=
  (p.map fun a => BernsteinPolynomial.checked a.time 0 1*r 0^a.u*r 1^a.v*r 2^a.c).sum

theorem bound_nonnegative (p : Coefficients) {r : Fin 3 → ℚ} (hr : ∀ i, 0≤r i) :
    0≤bound p r := by
  apply List.sum_nonneg
  intro b hb
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (BernsteinPolynomial.checked_nonnegative _ _ _) (pow_nonneg (hr 0) _))
    (pow_nonneg (hr 1) _)) (pow_nonneg (hr 2) _)

theorem monomial_bound (a : Term) {x : Fin 3 → ℝ} {r : Fin 3 → ℚ}
    (hx : ∀ i, |x i|≤(r i:ℝ)) :
    |monomial a x| ≤ ((r 0^a.u*r 1^a.v*r 2^a.c:ℚ):ℝ) := by
  have h (i : Fin 3) (n : ℕ) : |x i|^n≤(r i:ℝ)^n :=
    pow_le_pow_left₀ (abs_nonneg _) (hx i) _
  simp only [monomial,abs_mul,abs_pow,Rat.cast_mul,Rat.cast_pow]
  exact mul_le_mul (mul_le_mul (h 0 _) (h 1 _) (by positivity)
    (pow_nonneg ((abs_nonneg _).trans (hx 0)) _)) (h 2 _) (by positivity)
    (mul_nonneg (pow_nonneg ((abs_nonneg _).trans (hx 0)) _)
      (pow_nonneg ((abs_nonneg _).trans (hx 1)) _))

theorem bound_sound (p : Coefficients) {x : Fin 3 → ℝ} {r : Fin 3 → ℚ}
    (hx : ∀ i, |x i|≤(r i:ℝ)) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |value p x t|≤(bound p r:ℝ) := by
  induction p with
  | nil => simp [bound]
  | cons a p ih =>
    have hb := BernsteinPolynomial.checked_sound a.time (show (0:ℚ)<1 by norm_num)
      (show t ∈ Set.Icc ((0:ℚ):ℝ) ((1:ℚ):ℝ) by simpa using ht)
    have hm := monomial_bound a hx
    have hnonneg : (0:ℝ)≤(BernsteinPolynomial.checked a.time 0 1:ℝ) := by
      exact_mod_cast BernsteinPolynomial.checked_nonnegative a.time 0 1
    have hprod := mul_le_mul hb hm (abs_nonneg _) hnonneg
    rw [value_cons]
    apply (abs_add_le _ _).trans
    have hterm : |termValue a x t| ≤ (BernsteinPolynomial.checked a.time 0 1:ℝ)*
        ((r 0^a.u*r 1^a.v*r 2^a.c:ℚ):ℝ) := by
      simpa only [termValue,abs_mul] using hprod
    have h := add_le_add hterm ih
    convert h using 1 <;> simp [bound] <;> ring

end GNC.ParameterPolynomial
