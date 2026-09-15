import GNC.Analysis.BoxCertificate
import GNC.Analysis.PolynomialBox
import GNC.Analysis.CircleQuery
import GNC.Analysis.ClippedPolynomial

/-! Uniform polynomial-ODE certificates with a retained constant parameter.

The same checker accepts ordinary time/parameter polynomials and reduced
rotation-circle polynomials. Neither candidate generator is trusted. Exact
arithmetic checks the entire residual, region closure and segment handoff.
-/
namespace GNC.ParametricBox
open PolynomialODE

structure Model (C : Type) where
  constant : ℚ → C
  add : C → C → C
  multiply : C → C → C
  scale : ℚ → C → C
  derivative : C → C
  atTime : C → ℚ → C
  bound : C → ℚ → ℚ → ℚ
  value : C → ℝ → ℝ → ℝ
  value_constant : ∀ c t θ, value (constant c) t θ = (c : ℝ)
  value_add : ∀ p q t θ, value (add p q) t θ = value p t θ + value q t θ
  value_multiply : ∀ p q t θ, value (multiply p q) t θ = value p t θ * value q t θ
  value_scale : ∀ a p t θ, value (scale a p) t θ = (a : ℝ) * value p t θ
  value_derivative : ∀ p t θ,
    HasDerivAt (fun s => value p s θ) (value (derivative p) t θ) t
  value_atTime : ∀ p h t θ, value (atTime p h) t θ = value p (h : ℝ) θ
  bound_sound : ∀ p {h a : ℚ} {t θ : ℝ}, |t| ≤ (h : ℝ) → |θ| ≤ (a : ℝ) →
    |value p t θ| ≤ (bound p h a : ℝ)

noncomputable def polynomial : Model BivariatePolynomial.Coefficients where
  constant := fun c => [[c]]
  add := BivariatePolynomial.add
  multiply := BivariatePolynomial.multiply
  scale := BivariatePolynomial.scale
  derivative := BivariatePolynomial.derivative
  atTime := fun p h => [BivariatePolynomial.atTime p h]
  bound := BivariatePolynomial.bound
  value := BivariatePolynomial.value
  value_constant := by
    intros
    simp [BivariatePolynomial.value, BivariatePolynomial.slice, BivariatePolynomial.row,
      Planning.PolynomialKernel.evaluate]
  value_add := BivariatePolynomial.value_add
  value_multiply := BivariatePolynomial.value_multiply
  value_scale := BivariatePolynomial.value_scale
  value_derivative := BivariatePolynomial.value_derivative
  value_atTime := by
    intro p h t θ
    change BivariatePolynomial.row (BivariatePolynomial.atTime p h) θ + t * 0 = _
    rw [BivariatePolynomial.row_atTime, mul_zero, add_zero]
  bound_sound := fun p {_ _} {_ _} ht hθ => BivariatePolynomial.bound_sound p ht hθ

noncomputable def circle : Model CirclePolynomial.Coefficients where
  constant := fun c => ⟨[[c]], []⟩
  add := CirclePolynomial.add
  multiply := CirclePolynomial.multiply
  scale := CirclePolynomial.scale
  derivative := CirclePolynomial.derivative
  atTime := CircleQuery.atTime
  bound := CirclePolynomial.bound
  value := CirclePolynomial.value
  value_constant := by
    intros
    simp [CirclePolynomial.value, BivariatePolynomial.value, BivariatePolynomial.slice,
      BivariatePolynomial.row, Planning.PolynomialKernel.evaluate]
  value_add := CirclePolynomial.value_add
  value_multiply := CirclePolynomial.value_multiply
  value_scale := CirclePolynomial.value_scale
  value_derivative := CirclePolynomial.value_derivative
  value_atTime := CircleQuery.value_atTime
  bound_sound := fun p {_ _} {_ _} ht hθ => CirclePolynomial.bound_sound p ht hθ

variable {C : Type} {n : ℕ} (A : Model C)

def substitute (e : Expr n) (q : Fin n → C) : C :=
  match e with
  | .constant c => A.constant c
  | .var i => q i
  | .add a b => A.add (substitute a q) (substitute b q)
  | .multiply a b => A.multiply (substitute a q) (substitute b q)
  | .negate a => A.scale (-1) (substitute a q)

def residual (f : Fin n → Expr n) (q : Fin n → C) (i : Fin n) : C :=
  A.add (substitute A (f i) q) (A.scale (-1) (A.derivative (q i)))

structure Step (C : Type) (n : ℕ) where
  coefficients : Fin n → C
  duration : ℚ
  angle : ℚ
  region : Fin n → ℚ
  initialError : Fin n → ℚ
  error : Fin n → ℚ
  defect : Fin n → ℚ

def Step.Valid (s : Step C n) (f : Fin n → Expr n) : Prop :=
  0 ≤ s.duration ∧ 0 ≤ s.angle ∧ ∀ i,
    0 ≤ s.region i ∧ 0 ≤ s.initialError i ∧ 0 < s.error i ∧ 0 ≤ s.defect i ∧
    s.initialError i + s.duration * ((f i).differenceMajorant s.region s.error + s.defect i) < s.error i ∧
    A.bound (s.coefficients i) s.duration s.angle + s.error i ≤ s.region i ∧
    A.bound (residual A f s.coefficients i) s.duration s.angle ≤ s.defect i

instance (s : Step C n) (f : Fin n → Expr n) : Decidable (s.Valid A f) := by
  unfold Step.Valid
  infer_instance

noncomputable section

def curve (q : Fin n → C) (θ t : ℝ) : Fin n → ℝ := fun i => A.value (q i) t θ

theorem substitute_value (e : Expr n) (q : Fin n → C) (t θ : ℝ) :
    A.value (substitute A e q) t θ = e.value (curve A q θ t) := by
  induction e with
  | constant c => simp [substitute, A.value_constant, Expr.value]
  | var i => rfl
  | add a b ha hb => simp [substitute, A.value_add, ha, hb, Expr.value]
  | multiply a b ha hb => simp [substitute, A.value_multiply, ha, hb, Expr.value]
  | negate a ha => simp [substitute, A.value_scale, ha, Expr.value]

theorem residual_value (f : Fin n → Expr n) (q : Fin n → C) (i : Fin n) (t θ : ℝ) :
    A.value (residual A f q i) t θ =
      (f i).value (curve A q θ t) - A.value (A.derivative (q i)) t θ := by
  simp [residual, A.value_add, A.value_scale, substitute_value, sub_eq_add_neg]

theorem curve_derivative (q : Fin n → C) (θ t : ℝ) :
    HasDerivAt (curve A q θ) (curve A (fun i => A.derivative (q i)) θ t) t :=
  hasDerivAt_pi.mpr (fun i => A.value_derivative (q i) t θ)

/-- Uniform in the retained parameter. The actual ODE is only needed in the
proposed state region, which is established by the first-exit argument. -/
theorem step_sound (s : Step C n) (f : Fin n → Expr n) (hs : s.Valid A f)
    (θ : ℝ) (hθ : |θ| ≤ (s.angle : ℝ)) (x : ℝ → Fin n → ℝ) (hx : Continuous x)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) s.duration, (∀ i, |x t i| ≤ (s.region i : ℝ)) →
      HasDerivAt x (fun i => (f i).value (x t)) t)
    (hi : ∀ i, |x 0 i - curve A s.coefficients θ 0 i| ≤ (s.initialError i : ℝ)) :
    ∀ t ∈ Set.Icc (0 : ℝ) s.duration, ∀ i,
      |x t i - curve A s.coefficients θ t i| < (s.error i : ℝ) := by
  let p := curve A s.coefficients θ
  let v := curve A (fun i => A.derivative (s.coefficients i)) θ
  have hB (i) : (0 : ℝ) < s.error i := by exact_mod_cast (hs.2.2 i).2.2.1
  have hM (i) : 0 ≤ s.region i := (hs.2.2 i).1
  have hBn (i) : 0 ≤ s.error i := (hs.2.2 i).2.2.1.le
  have hC (i) : (0 : ℝ) ≤ (f i).differenceMajorant s.region s.error + s.defect i := by
    exact_mod_cast add_nonneg ((f i).differenceMajorant_nonneg hM hBn) (hs.2.2 i).2.2.2.1
  have hclose (i) : (s.initialError i : ℝ) + (s.duration : ℝ) *
      ((f i).differenceMajorant s.region s.error + s.defect i) < s.error i := by
    exact_mod_cast (hs.2.2 i).2.2.2.2.1
  have hp : Continuous p := continuous_iff_continuousAt.mpr
    (fun t => (curve_derivative A s.coefficients θ t).continuousAt)
  have hpoly (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) s.duration) (i : Fin n) :
      |p t i| + (s.error i : ℝ) ≤ s.region i := by
    have hb := A.bound_sound (s.coefficients i)
      (show |t| ≤ (s.duration : ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2) hθ
    have hr : (A.bound (s.coefficients i) s.duration s.angle : ℝ) + s.error i ≤ s.region i := by
      exact_mod_cast (hs.2.2 i).2.2.2.2.2.1
    change |p t i| ≤ _ at hb
    linarith
  have hregion (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) s.duration)
      (herr : ∀ i, |x t i - p t i| ≤ (s.error i : ℝ)) (i : Fin n) :
      |x t i| ≤ (s.region i : ℝ) := by
    have ha := abs_add_le (x t i - p t i) (p t i)
    rw [sub_add_cancel] at ha
    linarith [herr i, hpoly t ht i]
  apply BoxCertificate.response (fun t => x t - p t)
    (fun t i => (f i).value (x t) - v t i) (fun i => (s.error i : ℝ))
    (fun i => (f i).differenceMajorant s.region s.error + s.defect i)
    (fun i => (s.initialError i : ℝ)) (by exact_mod_cast hs.1) hB hC hclose (hx.sub hp) hi
  · intro t ht herr
    exact (hd t ht (hregion t ht herr)).sub (curve_derivative A s.coefficients θ t)
  · intro t ht herr i
    have hlip := (f i).box_difference_bound hM hBn (x t) (p t)
      (hregion t ht herr) (fun j => by linarith [hpoly t ht j, hB j]) herr
    have hr := A.bound_sound (residual A f s.coefficients i)
      (show |t| ≤ (s.duration : ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2) hθ
    rw [residual_value] at hr
    have hδ : (A.bound (residual A f s.coefficients i) s.duration s.angle : ℝ) ≤ s.defect i := by
      exact_mod_cast (hs.2.2 i).2.2.2.2.2.2
    have ha := abs_add_le ((f i).value (x t) - (f i).value (p t))
      ((f i).value (p t) - v t i)
    rw [sub_add_sub_cancel] at ha
    change |(f i).value (p t) - v t i| ≤ _ at hr
    linarith

end

def Step.Compatible (s next : Step C n) : Prop :=
  s.angle = next.angle ∧ ∀ i,
    A.bound (A.add (A.atTime (s.coefficients i) s.duration)
      (A.scale (-1) (A.atTime (next.coefficients i) 0))) 0 s.angle + s.error i ≤ next.initialError i

instance (s next : Step C n) : Decidable (s.Compatible A next) := by
  unfold Step.Compatible
  infer_instance

noncomputable section

theorem handoff (s next : Step C n) (hc : s.Compatible A next)
    {θ : ℝ} (hθ : |θ| ≤ (s.angle : ℝ)) (x : Fin n → ℝ)
    (hx : ∀ i, |x i - curve A s.coefficients θ s.duration i| ≤ (s.error i : ℝ)) :
    ∀ i, |x i - curve A next.coefficients θ 0 i| ≤ (next.initialError i : ℝ) := by
  intro i
  have hb := A.bound_sound (A.add (A.atTime (s.coefficients i) s.duration)
    (A.scale (-1) (A.atTime (next.coefficients i) 0))) (t := 0) (h := 0) (by norm_num) hθ
  simp only [A.value_add, A.value_scale, A.value_atTime, Rat.cast_neg, Rat.cast_one,
    Rat.cast_zero, neg_one_mul, ← sub_eq_add_neg] at hb
  have hcast : (A.bound (A.add (A.atTime (s.coefficients i) s.duration)
    (A.scale (-1) (A.atTime (next.coefficients i) 0))) 0 s.angle : ℝ) + s.error i ≤ next.initialError i := by
    exact_mod_cast hc.2 i
  have ha := abs_add_le (x i - curve A s.coefficients θ s.duration i)
    (curve A s.coefficients θ s.duration i - curve A next.coefficients θ 0 i)
  rw [sub_add_sub_cancel] at ha
  change |curve A s.coefficients θ s.duration i - curve A next.coefficients θ 0 i| ≤ _ at hb
  linarith [hx i]

theorem region_of_enclosure (s : Step C n) (f : Fin n → Expr n) (hs : s.Valid A f)
    {θ t : ℝ} (hθ : |θ| ≤ (s.angle : ℝ)) (ht : t ∈ Set.Icc (0 : ℝ) s.duration)
    (x : Fin n → ℝ)
    (hx : ∀ i, |x i - curve A s.coefficients θ t i| ≤ (s.error i : ℝ)) :
    ∀ i, |x i| ≤ (s.region i : ℝ) := by
  intro i
  have hp := A.bound_sound (s.coefficients i)
    (show |t| ≤ (s.duration : ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2) hθ
  have hr : (A.bound (s.coefficients i) s.duration s.angle : ℝ) + s.error i ≤ s.region i := by
    exact_mod_cast (hs.2.2 i).2.2.2.2.2.1
  have ha := abs_add_le (x i - curve A s.coefficients θ t i)
    (curve A s.coefficients θ t i)
  rw [sub_add_cancel] at ha
  change |curve A s.coefficients θ t i| ≤ _ at hp
  linarith [hx i]

/-- A terminal query is evaluated before taking absolute bounds, retaining
parameter correlation between position and velocity or between coordinates. -/
theorem terminal_query (s : Step C n) (f : Fin n → Expr n) (hs : s.Valid A f)
    (e : Expr n) {θ : ℝ} (hθ : |θ| ≤ (s.angle : ℝ)) (x : Fin n → ℝ)
    (hx : ∀ i, |x i-curve A s.coefficients θ s.duration i| ≤ (s.error i : ℝ)) :
    |e.value x| ≤ (A.bound (A.atTime (substitute A e s.coefficients) s.duration)
      0 s.angle + e.differenceMajorant s.region s.error : ℚ) := by
  have hM (i) : 0 ≤ s.region i := (hs.2.2 i).1
  have hB (i) : 0 ≤ s.error i := (hs.2.2 i).2.2.1.le
  have ht : (0 : ℝ) ≤ s.duration := by exact_mod_cast hs.1
  have hreg := region_of_enclosure A s f hs hθ ⟨ht,le_rfl⟩ x hx
  have hq (i) : |curve A s.coefficients θ s.duration i| ≤ (s.region i : ℝ) := by
    have hb := A.bound_sound (s.coefficients i)
      (show |(s.duration : ℝ)| ≤ (s.duration : ℝ) by rw [abs_of_nonneg ht]) hθ
    have hr : (A.bound (s.coefficients i) s.duration s.angle : ℝ) + s.error i ≤ s.region i := by
      exact_mod_cast (hs.2.2 i).2.2.2.2.2.1
    have he : (0 : ℝ) ≤ s.error i := by exact_mod_cast hB i
    change |curve A s.coefficients θ s.duration i| ≤ _ at hb
    linarith
  have hd := e.box_difference_bound hM hB x (curve A s.coefficients θ s.duration) hreg hq hx
  have hp := A.bound_sound (A.atTime (substitute A e s.coefficients) s.duration)
    (t := 0) (h := 0) (by norm_num) hθ
  rw [A.value_atTime, substitute_value] at hp
  have ha := abs_add_le (e.value x-e.value (curve A s.coefficients θ s.duration))
    (e.value (curve A s.coefficients θ s.duration))
  rw [sub_add_cancel] at ha
  push_cast
  linarith

/-- Combine a symbolic initial-state approximation with the checked
rounding/mismatch budget of the first candidate, in any state dimension. -/
theorem initial_enclosure (s : Step C n) (q₀ : Fin n → C) (δ : Fin n → ℚ)
    (hn : ∀ i, A.bound (A.add (q₀ i) (A.scale (-1) (A.atTime (s.coefficients i) 0)))
      0 s.angle+δ i ≤ s.initialError i)
    {θ : ℝ} (hθ : |θ| ≤ (s.angle : ℝ)) (z₀ : Fin n → ℝ)
    (hz : ∀ i, |z₀ i-A.value (q₀ i) 0 θ| ≤ (δ i : ℝ)) :
    ∀ i, |z₀ i-curve A s.coefficients θ 0 i| ≤ (s.initialError i : ℝ) := by
  intro i
  have hp := A.bound_sound (A.add (q₀ i) (A.scale (-1) (A.atTime (s.coefficients i) 0)))
    (t := 0) (h := 0) (by norm_num) hθ
  simp only [A.value_add, A.value_scale, A.value_atTime, Rat.cast_neg, Rat.cast_one,
    Rat.cast_zero, neg_one_mul, ← sub_eq_add_neg] at hp
  have hc : (A.bound (A.add (q₀ i) (A.scale (-1) (A.atTime (s.coefficients i) 0)))
      0 s.angle : ℝ)+δ i ≤ s.initialError i := by exact_mod_cast hn i
  have ha := abs_add_le (z₀ i-A.value (q₀ i) 0 θ)
    (A.value (q₀ i) 0 θ-A.value (s.coefficients i) 0 θ)
  rw [sub_add_sub_cancel] at ha
  change |z₀ i-A.value (s.coefficients i) 0 θ| ≤ _
  linarith [hz i]

/-- Validity also supports existence, not just a conditional enclosure.
Clipping constructs a global auxiliary solution; the certificate proves that
the clipping never changes the field on the claimed interval. -/
theorem exists_step (s : Step C n) (f : Fin n → Expr n) (hs : s.Valid A f)
    {θ : ℝ} (hθ : |θ| ≤ (s.angle : ℝ)) (x₀ : Fin n → ℝ)
    (hi : ∀ i, |x₀ i - curve A s.coefficients θ 0 i| ≤ (s.initialError i : ℝ))
    {R : ℚ} (hR : 0 ≤ R) (hregion : ∀ i, s.region i ≤ R)
    (K L : NNReal) (hK : ∀ i, ((f i).slope R : ℝ) ≤ K)
    (hL : ∀ i, ((f i).majorant R : ℝ) ≤ L) :
    ∃ x : ℝ → Fin n → ℝ, Continuous x ∧ x 0 = x₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) s.duration,
        HasDerivAt x (fun i => (f i).value (x t)) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) s.duration, ∀ i,
        |x t i - curve A s.coefficients θ t i| < (s.error i : ℝ)) := by
  obtain ⟨x, hx, hx₀, hd⟩ := clippedField_exists f hR K L hK hL x₀
    (show (0 : ℝ) ≤ s.duration by exact_mod_cast hs.1)
  have he := step_sound A s f hs θ hθ x hx (by
    intro t ht hr
    have hcast (i) : (s.region i : ℝ) ≤ R := by exact_mod_cast hregion i
    simpa only [clippedField_eq f (fun i => (hr i).trans (hcast i))] using hd t ht)
    (by simpa only [hx₀] using hi)
  refine ⟨x, hx, hx₀, ?_, he⟩
  intro t ht
  have hr := region_of_enclosure A s f hs hθ ht (x t) (fun i => (he t ht i).le)
  have hcast (i) : (s.region i : ℝ) ≤ R := by exact_mod_cast hregion i
  simpa only [clippedField_eq f (fun i => (hr i).trans (hcast i))] using hd t ht

/-- Finite polynomial fields automatically supply the coarse global bounds
needed by the clipped existence construction. They do not enter the error
budget of `Step.Valid`. -/
theorem exists_step_auto (s : Step C n) (f : Fin n → Expr n) (hs : s.Valid A f)
    {θ : ℝ} (hθ : |θ| ≤ (s.angle : ℝ)) (x₀ : Fin n → ℝ)
    (hi : ∀ i, |x₀ i - curve A s.coefficients θ 0 i| ≤ (s.initialError i : ℝ))
    {R : ℚ} (hR : 0 ≤ R) (hr : ∀ i, s.region i ≤ R) :
    ∃ x : ℝ → Fin n → ℝ, Continuous x ∧ x 0 = x₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) s.duration,
        HasDerivAt x (fun i => (f i).value (x t)) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) s.duration, ∀ i,
        |x t i - curve A s.coefficients θ t i| < (s.error i : ℝ)) := by
  let k : Fin n → NNReal := fun i => ⟨(f i).slope R, by exact_mod_cast (f i).slope_nonneg hR⟩
  let l : Fin n → NNReal := fun i => ⟨(f i).majorant R, by exact_mod_cast (f i).majorant_nonneg hR⟩
  apply exists_step A s f hs hθ x₀ hi hR hr (∑ i, k i) (∑ i, l i)
  · intro i
    exact_mod_cast (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (k j).coe_nonneg)
      (Finset.mem_univ i) : (k i : ℝ) ≤ ∑ j, (k j : ℝ))
  · intro i
    exact_mod_cast (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (l j).coe_nonneg)
      (Finset.mem_univ i) : (l i : ℝ) ≤ ∑ j, (l j : ℝ))

/-- A compatible finite certificate constructs all solution segments with
the same parameter and the actual terminal state as the next initial state. -/
theorem exists_segments (S : ℕ → Step C n) (f : ℕ → Fin n → Expr n) (N : ℕ)
    (hvalid : ∀ j < N, (S j).Valid A (f j))
    (hjoin : ∀ j, j+1 < N → (S j).Compatible A (S (j+1)))
    (θ : ℝ) (hθ : ∀ j < N, |θ| ≤ ((S j).angle : ℝ))
    (x₀ : Fin n → ℝ)
    (hi : ∀ i, |x₀ i - curve A (S 0).coefficients θ 0 i| ≤ ((S 0).initialError i : ℝ))
    {R : ℚ} (hR : 0 ≤ R) (hr : ∀ j < N, ∀ i, (S j).region i ≤ R) :
    ∃ x : ℕ → ℝ → Fin n → ℝ,
      (∀ j < N, Continuous (x j)) ∧ x 0 0 = x₀ ∧
      (∀ j < N, ∀ t ∈ Set.Icc (0 : ℝ) (S j).duration,
        HasDerivAt (x j) (fun i => (f j i).value (x j t)) t) ∧
      (∀ j < N, ∀ t ∈ Set.Icc (0 : ℝ) (S j).duration, ∀ i,
        |x j t i - curve A (S j).coefficients θ t i| < ((S j).error i : ℝ)) ∧
      (∀ j, j+1 < N → x (j+1) 0 = x j (S j).duration) := by
  induction N generalizing S f x₀ with
  | zero =>
    exact ⟨fun _ _ => x₀, by simp⟩
  | succ N ih =>
    obtain ⟨y, hy, hy0, hyd, hye⟩ := exists_step_auto A (S 0) (f 0)
      (hvalid 0 (by omega)) (hθ 0 (by omega)) x₀ hi hR (hr 0 (by omega))
    by_cases hN : N = 0
    · subst N
      refine ⟨fun _ => y, ?_, hy0, ?_, ?_, ?_⟩
      · intro j hj
        exact hy
      · intro j hj
        have : j = 0 := by omega
        subst j
        exact hyd
      · intro j hj
        have : j = 0 := by omega
        subst j
        exact hye
      · omega
    have ht : (0 : ℝ) ≤ (S 0).duration := by exact_mod_cast (hvalid 0 (by omega)).1
    have hi' := handoff A (S 0) (S 1) (hjoin 0 (by omega)) (hθ 0 (by omega))
      (y (S 0).duration) (fun i => (hye (S 0).duration ⟨ht,le_rfl⟩ i).le)
    obtain ⟨tail, hc, h0, hd, he, hj⟩ := ih (fun j => S (j+1)) (fun j => f (j+1))
      (fun j hj => hvalid (j+1) (by omega))
      (fun j hj => hjoin (j+1) (by omega))
      (fun j hj => hθ (j+1) (by omega)) (y (S 0).duration) hi'
      (fun j hj => hr (j+1) (by omega))
    let x : ℕ → ℝ → Fin n → ℝ := fun j => Nat.casesOn j y tail
    refine ⟨x, ?_, hy0, ?_, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => exact hy
      | succ j => exact hc j (by omega)
    · intro j hj
      cases j with
      | zero => exact hyd
      | succ j => exact hd j (by omega)
    · intro j hj
      cases j with
      | zero => exact hye
      | succ j => exact he j (by omega)
    · intro j hj'
      cases j with
      | zero => exact h0
      | succ j => exact hj j (by omega)

/-- One retained parameter is shared by every burn and coast segment. It is
not reset independently at a command switch. -/
theorem segments_sound (S : ℕ → Step C n) (f : ℕ → Fin n → Expr n) (N : ℕ)
    (hvalid : ∀ j < N, (S j).Valid A (f j))
    (hjoin : ∀ j, j+1 < N → (S j).Compatible A (S (j+1)))
    (θ : ℝ) (hθ : ∀ j < N, |θ| ≤ ((S j).angle : ℝ))
    (x : ℕ → ℝ → Fin n → ℝ) (hx : ∀ j < N, Continuous (x j))
    (hd : ∀ j < N, ∀ t ∈ Set.Icc (0 : ℝ) (S j).duration,
      HasDerivAt (x j) (fun i => (f j i).value (x j t)) t)
    (hjx : ∀ j, j+1 < N → x (j+1) 0 = x j (S j).duration)
    (hi : ∀ i, |x 0 0 i - curve A (S 0).coefficients θ 0 i| ≤ ((S 0).initialError i : ℝ)) :
    ∀ j < N, ∀ t ∈ Set.Icc (0 : ℝ) (S j).duration, ∀ i,
      |x j t i - curve A (S j).coefficients θ t i| < ((S j).error i : ℝ) := by
  intro j
  induction j with
  | zero =>
    intro hj
    exact step_sound A (S 0) (f 0) (hvalid 0 hj) θ (hθ 0 hj) (x 0) (hx 0 hj)
      (fun t ht _ => hd 0 hj t ht) hi
  | succ j ih =>
    intro hj
    have hj' : j < N := by omega
    have ht : (0 : ℝ) ≤ (S j).duration := by exact_mod_cast (hvalid j hj').1
    have hp := ih hj' (S j).duration ⟨ht, le_rfl⟩
    have hi' := handoff A (S j) (S (j+1)) (hjoin j hj) (hθ j hj')
      (x j (S j).duration) (fun i => (hp i).le)
    rw [← hjx j hj] at hi'
    exact step_sound A (S (j+1)) (f (j+1)) (hvalid (j+1) hj) θ (hθ (j+1) hj)
      (x (j+1)) (hx (j+1) hj) (fun t ht _ => hd (j+1) hj t ht) hi'

end
end GNC.ParametricBox
