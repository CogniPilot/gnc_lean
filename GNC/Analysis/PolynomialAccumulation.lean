import GNC.Analysis.PolynomialIntegral

/-! A posteriori bounds for accumulated, piecewise continuous forcing.
The polynomial pieces may have different coordinate origins and nonzero
jumps. Initial, integrand and jump errors add; no transition norm is applied
again at each subdivision. All bounds include an arbitrary final partial arc.
-/
namespace GNC.PolynomialAccumulation
open Planning.PolynomialKernel PolynomialBounds PolynomialIntegral

noncomputable def value (cs : List ℚ) (d t : ℝ) : ℝ :=
  evaluate (cs.map (Rat.castHom ℝ)) (t-d)

noncomputable def rate (cs : List ℚ) (d t : ℝ) : ℝ :=
  evaluate ((differentiate cs).map (Rat.castHom ℝ)) (t-d)

theorem value_derivative (cs : List ℚ) (d t : ℝ) :
    HasDerivAt (value cs d) (rate cs d t) t := by
  have h := (evaluate_hasDerivAt (cs.map (Rat.castHom ℝ)) (t-d)).comp t
    ((hasDerivAt_id t).sub_const d)
  simpa only [differentiate_map, mul_one] using h

theorem rate_continuous (cs : List ℚ) (d : ℝ) : Continuous (rate cs d) :=
  (evaluate_continuous _).comp (continuous_id.sub continuous_const)

theorem increment_error (cs : List ℚ) (d : ℝ) (f : ℝ → ℝ) {a b D : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (he : ∀ t ∈ Set.Icc a b, |f t-rate cs d t| ≤ D) :
    |(∫ t in a..b, f t)-(value cs d b-value cs d a)| ≤ (b-a)*D := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => value_derivative cs d t) ((rate_continuous cs d).intervalIntegrable a b)
  have h := integral_error f (rate cs d) hab hf
    ((rate_continuous cs d).intervalIntegrable a b) he
  rwa [hi] at h

noncomputable def boundary (x₀ : ℝ) (f : ℕ → ℝ → ℝ) (nodes : ℕ → ℝ) (n : ℕ) : ℝ :=
  x₀+∑ k ∈ Finset.range n, ∫ t in nodes k..nodes (k+1), f k t

theorem boundary_zero (x₀ : ℝ) (f : ℕ → ℝ → ℝ) (nodes : ℕ → ℝ) :
    boundary x₀ f nodes 0 = x₀ := by simp [boundary]

theorem boundary_succ (x₀ : ℝ) (f : ℕ → ℝ → ℝ) (nodes : ℕ → ℝ) (n : ℕ) :
    boundary x₀ f nodes (n+1) =
      boundary x₀ f nodes n+∫ t in nodes n..nodes (n+1), f n t := by
  simp [boundary, Finset.sum_range_succ, add_assoc]

theorem boundary_error (x₀ : ℝ) (f : ℕ → ℝ → ℝ) (nodes origins : ℕ → ℝ)
    (cs : ℕ → List ℚ) (n : ℕ) {E D J : ℝ}
    (hi : |x₀-value (cs 0) (origins 0) (nodes 0)| ≤ E)
    (ho : ∀ k < n, nodes k ≤ nodes (k+1))
    (hf : ∀ k < n, IntervalIntegrable (f k) MeasureTheory.volume (nodes k) (nodes (k+1)))
    (he : ∀ k < n, ∀ t ∈ Set.Icc (nodes k) (nodes (k+1)),
      |f k t-rate (cs k) (origins k) t| ≤ D)
    (hj : ∀ k < n,
      |value (cs k) (origins k) (nodes (k+1))-
        value (cs (k+1)) (origins (k+1)) (nodes (k+1))| ≤ J) :
    |boundary x₀ f nodes n-value (cs n) (origins n) (nodes n)| ≤
      E+(n:ℝ)*J+(nodes n-nodes 0)*D := by
  induction n with
  | zero => simpa only [boundary_zero, Nat.cast_zero, zero_mul, sub_self, add_zero] using hi
  | succ n ih =>
    have hprev := ih (fun k hk => ho k (by omega)) (fun k hk => hf k (by omega))
      (fun k hk => he k (by omega)) (fun k hk => hj k (by omega))
    have hinc := increment_error (cs n) (origins n) (f n)
      (ho n (by omega)) (hf n (by omega)) (he n (by omega))
    have hsplit := abs_add_le
      (boundary x₀ f nodes n-value (cs n) (origins n) (nodes n))
      ((∫ t in nodes n..nodes (n+1), f n t)-
        (value (cs n) (origins n) (nodes (n+1))-value (cs n) (origins n) (nodes n)))
    have hsum : boundary x₀ f nodes n-value (cs n) (origins n) (nodes n)+
        ((∫ t in nodes n..nodes (n+1), f n t)-
          (value (cs n) (origins n) (nodes (n+1))-value (cs n) (origins n) (nodes n))) =
        boundary x₀ f nodes (n+1)-value (cs n) (origins n) (nodes (n+1)) := by
      rw [boundary_succ]; ring
    rw [hsum] at hsplit
    have hlast := abs_sub_le (boundary x₀ f nodes (n+1))
      (value (cs n) (origins n) (nodes (n+1)))
      (value (cs (n+1)) (origins (n+1)) (nodes (n+1)))
    have hjoin := hj n (by omega)
    push_cast
    nlinarith

/-- Every prefix, including a partial last arc, with all discontinuities of
the polynomial proposal charged explicitly. The actual forcing need only be
integrable separately on the arcs. -/
theorem prefix_error (x₀ : ℝ) (f : ℕ → ℝ → ℝ) (nodes origins : ℕ → ℝ)
    (cs : ℕ → List ℚ) (n : ℕ) {T E D J : ℝ}
    (hi : |x₀-value (cs 0) (origins 0) (nodes 0)| ≤ E)
    (ho : ∀ k < n, nodes k ≤ nodes (k+1))
    (hf : ∀ k < n, IntervalIntegrable (f k) MeasureTheory.volume (nodes k) (nodes (k+1)))
    (he : ∀ k < n, ∀ t ∈ Set.Icc (nodes k) (nodes (k+1)),
      |f k t-rate (cs k) (origins k) t| ≤ D)
    (hj : ∀ k < n,
      |value (cs k) (origins k) (nodes (k+1))-
        value (cs (k+1)) (origins (k+1)) (nodes (k+1))| ≤ J)
    (hT : nodes n ≤ T)
    (hfi : IntervalIntegrable (f n) MeasureTheory.volume (nodes n) T)
    (hei : ∀ t ∈ Set.Icc (nodes n) T, |f n t-rate (cs n) (origins n) t| ≤ D) :
    |boundary x₀ f nodes n+(∫ t in nodes n..T, f n t)-value (cs n) (origins n) T| ≤
      E+(n:ℝ)*J+(T-nodes 0)*D := by
  have hb := boundary_error x₀ f nodes origins cs n hi ho hf he hj
  have hp := increment_error (cs n) (origins n) (f n) hT hfi hei
  have ht := abs_add_le
    (boundary x₀ f nodes n-value (cs n) (origins n) (nodes n))
    ((∫ t in nodes n..T, f n t)-(value (cs n) (origins n) T-value (cs n) (origins n) (nodes n)))
  have hsum : boundary x₀ f nodes n-value (cs n) (origins n) (nodes n)+
      ((∫ t in nodes n..T, f n t)-(value (cs n) (origins n) T-value (cs n) (origins n) (nodes n))) =
      boundary x₀ f nodes n+(∫ t in nodes n..T, f n t)-value (cs n) (origins n) T := by ring
  rw [hsum] at ht
  nlinarith

end GNC.PolynomialAccumulation
