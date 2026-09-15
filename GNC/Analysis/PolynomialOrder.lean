import GNC.Analysis.PolynomialBounds

/-! Exact sufficient order certificates for real polynomials on [0,1].
Nonnegative cumulative coefficients allow negative high-order coefficients:
a + t b = (1-t)a + t(a+b). Iterating this identity checks a useful family
of polynomial barriers without sampling, roots or an inflation tolerance.
-/
namespace GNC.PolynomialOrder
open Planning.PolynomialKernel

noncomputable def value (p : List ℚ) (t : ℝ) : ℝ :=
  evaluate (p.map (Rat.castHom ℝ)) t

def nonnegative (p : List ℚ) : Prop := ∀ a ∈ p, 0 ≤ a

def prefixes : ℚ → List ℚ → Prop
  | s,[] => 0 ≤ s
  | s,a::p => 0 ≤ s ∧ prefixes (s+a) p

instance (p : List ℚ) : Decidable (nonnegative p) := by
  unfold nonnegative
  infer_instance
instance (s : ℚ) (p : List ℚ) : Decidable (prefixes s p) := by
  induction p generalizing s with
  | nil => exact inferInstanceAs (Decidable (0 ≤ s))
  | cons a p ih => exact @instDecidableAnd _ _ inferInstance (ih (s+a))

theorem value_nonnegative (p : List ℚ) (hp : nonnegative p) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ value p t := by
  induction p with
  | nil => simp [value,evaluate]
  | cons a p ih =>
    have ha : (0:ℝ) ≤ a := by exact_mod_cast hp a (by simp)
    have hb := ih (fun b hb => hp b (by simp [hb]))
    change 0 ≤ (a:ℝ)+t*value p t
    positivity

theorem nonnegative_add (p q : List ℚ) (hp : nonnegative p) (hq : nonnegative q) :
    nonnegative (PolynomialBounds.add p q) := by
  induction p generalizing q with
  | nil => exact hq
  | cons a p ih =>
    cases q with
    | nil => exact hp
    | cons b q =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact add_nonneg (hp a (by simp)) (hq b (by simp))
      · exact ih q (fun c hc => hp c (by simp [hc]))
          (fun c hc => hq c (by simp [hc])) c hc

theorem nonnegative_scale {a : ℚ} (ha : 0 ≤ a) (p : List ℚ) (hp : nonnegative p) :
    nonnegative (PolynomialBounds.scale a p) := by
  intro c hc
  rcases List.mem_map.mp hc with ⟨b,hb,rfl⟩
  exact mul_nonneg ha (hp b hb)

theorem value_le_endpoint (p : List ℚ) (hp : nonnegative p) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : value p t ≤ value p 1 := by
  induction p with
  | nil => simp [value,evaluate]
  | cons a p ih =>
    have htail : nonnegative p := fun b hb => hp b (by simp [hb])
    have h := mul_le_mul ht.2 (ih htail) (value_nonnegative p htail ht.1) (by norm_num : (0:ℝ) ≤ 1)
    change (a:ℝ)+t*value p t ≤ (a:ℝ)+1*value p 1
    exact add_le_add_right h _

theorem prefix_value (s : ℚ) (p : List ℚ) (hp : prefixes s p) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 ≤ (s:ℝ)+t*value p t := by
  induction p generalizing s with
  | nil => simpa [value,evaluate] using (show (0:ℝ) ≤ s by exact_mod_cast hp)
  | cons a p ih =>
    have hs : (0:ℝ) ≤ s := by exact_mod_cast hp.1
    have hb := ih (s+a) hp.2
    have he : (s:ℝ)+t*value (a::p) t =
        (1-t)*(s:ℝ)+t*((s+a:ℚ)+t*value p t) := by
      change (s:ℝ)+t*((a:ℝ)+t*value p t) = _
      push_cast
      ring
    rw [he]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hs) (mul_nonneg ht.1 hb)

theorem prefixes_sound (p : List ℚ) (hp : prefixes 0 p) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 ≤ value p t := by
  cases p with
  | nil => simp [value,evaluate]
  | cons a p =>
    have h := prefix_value a p (by simpa only [zero_add] using hp.2) ht
    exact h

theorem value_derivative (p : List ℚ) (t : ℝ) :
    HasDerivAt (value p) (value (differentiate p) t) t := by
  simpa only [value,differentiate_map] using
    PolynomialBounds.evaluate_hasDerivAt (p.map (Rat.castHom ℝ)) t

theorem value_at_rational (p : List ℚ) (t : ℚ) :
    value p (t:ℝ) = ((evaluate p t:ℚ):ℝ) := evaluate_map (Rat.castHom ℝ) p t

/-- A zero initial value and slope retain the quadratic time factor in a
nonnegative coefficient envelope. -/
theorem quadratic_time_bound (p : List ℚ) (hp : nonnegative p)
    (hz : p = 0::0::p.drop 2) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    value p t ≤ t^2*value p 1 := by
  have htail : nonnegative (p.drop 2) :=
    fun a ha => hp a (List.mem_of_mem_drop ha)
  have he (s : ℝ) : value p s = s^2*value (p.drop 2) s := by
    conv_lhs => rw [hz]
    simp only [value,List.map_cons,evaluate,map_zero]
    ring
  rw [he t,he 1]
  norm_num only [one_pow,one_mul]
  exact mul_le_mul_of_nonneg_left (value_le_endpoint _ htail ht) (sq_nonneg t)

theorem value_add (p q : List ℚ) (t : ℝ) :
    value (PolynomialBounds.add p q) t = value p t+value q t := by
  unfold value
  rw [PolynomialBounds.add_map,PolynomialBounds.evaluate_add]

theorem value_scale (a : ℚ) (p : List ℚ) (t : ℝ) :
    value (PolynomialBounds.scale a p) t = (a:ℝ)*value p t := by
  unfold value
  rw [PolynomialBounds.scale_map,PolynomialBounds.evaluate_scale]
  rfl

theorem value_subtract (p q : List ℚ) (t : ℝ) :
    value (PolynomialBounds.subtract p q) t = value p t-value q t := by
  unfold value
  rw [PolynomialBounds.subtract_map,PolynomialBounds.evaluate_subtract]

end GNC.PolynomialOrder
