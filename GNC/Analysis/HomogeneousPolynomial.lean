import GNC.Analysis.PolynomialOrder
import Mathlib.Tactic

/-! A division-free polynomial positivity check on [0,1]. The exact lift
rewrites a power polynomial as a homogeneous polynomial in t and 1-t.
Nonnegative lifted coefficients suffice, including at both endpoints.
The Pascal recurrence is proved once; certificates need no separate
coefficient-reconstruction witness. -/
namespace GNC.HomogeneousPolynomial
open PolynomialBounds

def grow (previous : ℚ) : List ℚ → List ℚ
  | [] => [previous]
  | a::p => (previous+a)::grow a p

def pascal : ℕ → List ℚ
  | 0 => [1]
  | n+1 => grow 0 (pascal n)

def lift : List ℚ → List ℚ
  | [] => []
  | a::p => add (scale a (pascal p.length)) (0::lift p)

theorem grow_length (a : ℚ) (p : List ℚ) : (grow a p).length=p.length+1 := by
  induction p generalizing a with
  | nil => rfl
  | cons b p ih => simp [grow,ih]

theorem grow_eq (a : ℚ) (p : List ℚ) : grow a p=add (p++[0]) (a::p) := by
  induction p generalizing a with
  | nil => simp [grow,add]
  | cons b p ih => simp [grow,add,ih,add_comm]

theorem pascal_length (n : ℕ) : (pascal n).length=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pascal,grow_length,ih]

theorem add_length {p q : List ℚ} (h : p.length=q.length) : (add p q).length=p.length := by
  induction p generalizing q with
  | nil => simpa [add] using h.symm
  | cons a p ih =>
    cases q with
    | nil => simp at h
    | cons b q => simp only [List.length_cons,Nat.add_right_cancel_iff] at h
                  simp [add,ih h]

theorem lift_length (p : List ℚ) : (lift p).length=p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [lift]
    rw [add_length (by simp [scale,pascal_length,ih])]
    simp [scale,pascal_length]

noncomputable def value : List ℚ → ℝ → ℝ → ℝ
  | [],_,_ => 0
  | a::p,t,u => (a:ℝ)*u^p.length+t*value p t u

theorem value_add {p q : List ℚ} (h : p.length=q.length) (t u : ℝ) :
    value (add p q) t u=value p t u+value q t u := by
  induction p generalizing q with
  | nil =>
    have hq : q=[] := List.length_eq_zero_iff.mp h.symm
    simp [hq,add,value]
  | cons a p ih =>
    cases q with
    | nil => simp at h
    | cons b q =>
      have htail : p.length=q.length := by simpa using h
      simp only [add,value,add_length htail,Rat.cast_add,ih htail]
      rw [htail]
      ring

theorem value_scale (a : ℚ) (p : List ℚ) (t u : ℝ) :
    value (scale a p) t u=(a:ℝ)*value p t u := by
  induction p with
  | nil => simp [scale,value]
  | cons b p ih =>
    simp only [scale,List.map_cons,value,List.length_map,Rat.cast_mul] at *
    rw [ih]
    ring

theorem value_append_zero (p : List ℚ) (t u : ℝ) :
    value (p++[0]) t u=u*value p t u := by
  induction p with
  | nil => simp [value]
  | cons a p ih =>
    simp only [List.cons_append,value,List.length_append,List.length_singleton,pow_succ,ih]
    ring

theorem value_pascal (n : ℕ) (t u : ℝ) : value (pascal n) t u=(t+u)^n := by
  induction n with
  | zero => simp [pascal,value]
  | succ n ih =>
    rw [pascal,grow_eq,value_add (by simp)]
    simp only [value_append_zero,value,Rat.cast_zero,zero_mul,zero_add,ih]
    rw [pow_succ]
    ring

theorem value_lift (p : List ℚ) (t u : ℝ) (h : t+u=1) :
    value (lift p) t u=PolynomialOrder.value p t := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [lift,value_add (by simp [scale,pascal_length,lift_length]),value_scale,value_pascal]
    simp only [value,Rat.cast_zero,zero_mul,zero_add,ih,h,one_pow,mul_one]
    rfl

theorem value_nonnegative (p : List ℚ) (hp : PolynomialOrder.nonnegative p)
    {t u : ℝ} (ht : 0≤t) (hu : 0≤u) : 0≤value p t u := by
  induction p with
  | nil => exact le_rfl
  | cons a p ih =>
    have ha : (0:ℝ)≤a := by exact_mod_cast hp a (by simp)
    have hb := ih (fun b hb => hp b (by simp [hb]))
    exact add_nonneg (mul_nonneg ha (pow_nonneg hu _)) (mul_nonneg ht hb)

/-- An exact finite coefficient check certifies the entire real interval. -/
theorem certifies (p : List ℚ) (hp : PolynomialOrder.nonnegative (lift p))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : 0≤PolynomialOrder.value p t := by
  have h := value_nonnegative (lift p) hp ht.1 (sub_nonneg.mpr ht.2)
  rwa [value_lift p t (1-t) (by ring)] at h

end GNC.HomogeneousPolynomial
