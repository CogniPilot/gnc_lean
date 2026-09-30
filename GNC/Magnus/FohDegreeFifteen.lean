import GNC.Magnus.FohDegreeFifteenFlow
import GNC.Magnus.FohDegreeFifteenPowers
import GNC.Magnus.FohDegreeFifteenEndpoints

/-!
# The degree-fifteen finite formal FOH logarithm

For midpoint angular velocity `m` and slope `s`, rescale the interval to
`u ∈ [-1/2,1/2]`. The formal right-quaternion equation is
`∂u Q(h,u) = Q(h,u) * (h m + h² u s) / 2`, with `Q(h,-1/2) = 1`.
Its coefficient recurrence is proved for the explicit polynomial `solution`.

`exponent_coefficient_table` identifies `exponentPolynomial` with half the
rotation-vector coefficient table. `exponential_matches_solution` proves its
formal quaternion exponential equals the endpoint of this flow through degree
fifteen. `formal_log_through_fifteen` gives the same conclusion for every
polynomial coefficient family satisfying the defining flow recurrence and
normalization. Existence and uniqueness are both established within this
finite setting; no desired endpoint equality is assumed.

The arithmetic certificates are separated into cached modules. All equalities
are checked by Lean's kernel. This result makes no analytic convergence or
actual-log Taylor assertion.
-/

noncomputable section
open Matrix Polynomial
open scoped Quaternion Matrix
namespace GNC.Magnus
namespace DegreeFifteen

theorem q_recurrence (f g z : ℝ) (n : ℕ) (hn : n < 15) (j : ℕ) :
    ((j+1:ℕ):ℝ) • qData f g z (n+1) (j+1) = (1/2:ℝ) •
      (product f g z (qData f g z n j) firstQuad +
       if j = 0 ∨ n = 0 then 0 else
         product f g z (qData f g z (n-1) (j-1)) secondQuad) := by
  by_cases hj : j < 16
  · interval_cases n
    all_goals first
      | exact q_recurrence_0 f g z j hj
      | exact q_recurrence_1 f g z j hj
      | exact q_recurrence_2 f g z j hj
      | exact q_recurrence_3 f g z j hj
      | exact q_recurrence_4 f g z j hj
      | exact q_recurrence_5 f g z j hj
      | exact q_recurrence_6 f g z j hj
      | exact q_recurrence_7 f g z j hj
      | exact q_recurrence_8 f g z j hj
      | exact q_recurrence_9 f g z j hj
      | exact q_recurrence_10 f g z j hj
      | exact q_recurrence_11 f g z j hj
      | exact q_recurrence_12 f g z j hj
      | exact q_recurrence_13 f g z j hj
      | exact q_recurrence_14 f g z j hj
  · rw [qData_support f g z (n+1) (j+1) (by omega),
      qData_support f g z n j (by omega),
      qData_degree f g z (n-1) (j-1) (by omega)]
    simp [product_zero_left]

def solution (m s : Vec3) (n : ℕ) : Polynomial ℍ :=
  poly (qData (fohDot m m) (fohDot s s) (fohDot m s) n) m s

def exponentPolynomial (m s : Vec3) : Polynomial ℍ :=
  poly (exponentData (fohDot m m) (fohDot s s) (fohDot m s)) m s

theorem exponent_constant_zero (m s : Vec3) :
    (exponentPolynomial m s).coeff 0 = 0 := by
  simp [exponentPolynomial, poly_coeff, exponentData]

/-- No omitted exponential power contributes to a checked coefficient. -/
theorem exponent_power_vanishes (m s : Vec3) (k n : ℕ) (hn : n < k) :
    ((exponentPolynomial m s)^k).coeff n = 0 :=
  coeff_pow_vanishes _ (exponent_constant_zero m s) k n hn

/-- Each quaternion exponent coefficient is exactly half the displayed
rotational-vector coefficient in the invariant basis. -/
theorem exponent_coefficient_table (m s : Vec3) (n : ℕ) (hn : n ≤ 15) :
    (exponentPolynomial m s).coeff n = (1/2:ℝ) •
      embed m s (tableData (fohDot m m) (fohDot s s) (fohDot m s) n) := by
  rw [exponentPolynomial, poly_coeff, if_pos (by omega),
    exponent_half_table _ _ _ n (by omega), map_smul]

theorem solution_derivative (m s : Vec3) (n : ℕ) (hn : n < 15) :
    (solution m s (n+1)).derivative = (1/2:ℝ) •
      (solution m s n * C (embed m s firstQuad) +
       X * (if n = 0 then 0 else solution m s (n-1)) * C (embed m s secondQuad)) := by
  have hh := poly_derivative_from_certificate m s
    (qData (fohDot m m) (fohDot s s) (fohDot m s) (n+1))
    (qData (fohDot m m) (fohDot s s) (fohDot m s) n)
    (if n = 0 then fun _ => 0 else qData (fohDot m m) (fohDot s s) (fohDot m s) (n-1))
    (qData_support _ _ _ _) (qData_support _ _ _ _) (by
      intro j hj
      split_ifs
      · rfl
      · exact qData_support _ _ _ _ j hj) (by
      intro j
      have he := q_recurrence (fohDot m m) (fohDot s s) (fohDot m s) n hn j
      by_cases hn0 : n = 0 <;> simpa [hn0, product_zero_left] using he)
  by_cases hn0 : n = 0
  · simpa [solution, hn0, poly] using hh
  · simpa [solution, hn0] using hh

theorem solution_zero (m s : Vec3) : solution m s 0 = 1 := by
  apply Polynomial.ext
  intro n
  by_cases hn : n = 0
  · subst n
    rw [solution, poly_coeff, if_pos (by omega)]
    simpa [qData, qData_0, qData_0_0, qData_0_0_0, oneQuad] using embed_one m s
  · simp [solution, poly_coeff, qData, qData_0, hn, Polynomial.coeff_one]

theorem solution_boundary (m s : Vec3) (n : ℕ) (hn : n < 15) :
    (solution m s (n+1)).eval (-1/2) = 0 := by
  have hc : ((-1/2:ℝ):ℍ) = (-1/2:ℍ) := by
    rw [Quaternion.coe_div, Quaternion.coe_neg]
    rfl
  rw [← hc]
  rw [solution, poly_eval_real]
  interval_cases n
  all_goals first
    | rw [q_boundary_1, map_zero]
    | rw [q_boundary_2, map_zero]
    | rw [q_boundary_3, map_zero]
    | rw [q_boundary_4, map_zero]
    | rw [q_boundary_5, map_zero]
    | rw [q_boundary_6, map_zero]
    | rw [q_boundary_7, map_zero]
    | rw [q_boundary_8, map_zero]
    | rw [q_boundary_9, map_zero]
    | rw [q_boundary_10, map_zero]
    | rw [q_boundary_11, map_zero]
    | rw [q_boundary_12, map_zero]
    | rw [q_boundary_13, map_zero]
    | rw [q_boundary_14, map_zero]
    | rw [q_boundary_15, map_zero]

theorem power_steps (f g z : ℝ) (k : ℕ) (hk : k < 15) (n : ℕ) (hn : n < 16) :
    powerData f g z (k+1) n = convolution f g z (powerData f g z k) (exponentData f g z) n := by
  interval_cases k
  all_goals first
    | exact power_step_0 f g z n hn
    | exact power_step_1 f g z n hn
    | exact power_step_2 f g z n hn
    | exact power_step_3 f g z n hn
    | exact power_step_4 f g z n hn
    | exact power_step_5 f g z n hn
    | exact power_step_6 f g z n hn
    | exact power_step_7 f g z n hn
    | exact power_step_8 f g z n hn
    | exact power_step_9 f g z n hn
    | exact power_step_10 f g z n hn
    | exact power_step_11 f g z n hn
    | exact power_step_12 f g z n hn
    | exact power_step_13 f g z n hn
    | exact power_step_14 f g z n hn

theorem exponent_power_coeff (m s : Vec3) (k n : ℕ) (hk : k ≤ 15) (hn : n ≤ 15) :
    ((exponentPolynomial m s)^k).coeff n =
      embed m s (powerData (fohDot m m) (fohDot s s) (fohDot m s) k n) := by
  apply power_coeff_from_certificate m s _ _ _ _ k hk n (by omega)
  · intro j hj
    by_cases hj0 : j = 0
    · subst j; rfl
    · simp [powerData, powerData_0, hj0]
  · exact power_steps _ _ _

theorem exponential_matches_solution (m s : Vec3) (n : ℕ) (hn : n ≤ 15) :
    expCoeff (exponentPolynomial m s) n = (solution m s n).eval (1/2) := by
  have he : expCoeff (exponentPolynomial m s) n =
      embed m s (∑ k ∈ Finset.range (n+1), ((Nat.factorial k:ℝ)⁻¹) •
        powerData (fohDot m m) (fohDot s s) (fohDot m s) k n) := by
    simp only [expCoeff, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [exponent_power_coeff m s k n (by have := Finset.mem_range.mp hk; omega) hn]
  rw [he]
  have hc : ((1/2:ℝ):ℍ) = (1/2:ℍ) := by
    rw [Quaternion.coe_div]
    rfl
  rw [← hc]
  rw [solution, poly_eval_real]
  interval_cases n
  all_goals first
    | rw [exponential_endpoint_0, q_endpoint_0]
    | rw [exponential_endpoint_1, q_endpoint_1]
    | rw [exponential_endpoint_2, q_endpoint_2]
    | rw [exponential_endpoint_3, q_endpoint_3]
    | rw [exponential_endpoint_4, q_endpoint_4]
    | rw [exponential_endpoint_5, q_endpoint_5]
    | rw [exponential_endpoint_6, q_endpoint_6]
    | rw [exponential_endpoint_7, q_endpoint_7]
    | rw [exponential_endpoint_8, q_endpoint_8]
    | rw [exponential_endpoint_9, q_endpoint_9]
    | rw [exponential_endpoint_10, q_endpoint_10]
    | rw [exponential_endpoint_11, q_endpoint_11]
    | rw [exponential_endpoint_12, q_endpoint_12]
    | rw [exponential_endpoint_13, q_endpoint_13]
    | rw [exponential_endpoint_14, q_endpoint_14]
    | rw [exponential_endpoint_15, q_endpoint_15]

/-- The displayed finite rotational logarithm is characterized by its
exponential matching the unique normalized right-quaternion flow through
degree fifteen. This is a finite formal theorem, without an analytic
convergence or actual-log Taylor hypothesis. -/
theorem formal_log_through_fifteen (m s : Vec3) (Q : ℕ → Polynomial ℍ)
    (h0 : Q 0 = 1)
    (hb : ∀ n < 15, (Q (n+1)).eval (-1/2) = 0)
    (hQ : ∀ n < 15, (Q (n+1)).derivative = (1/2:ℝ) •
      (Q n * C (embed m s firstQuad) +
       X * (if n = 0 then 0 else Q (n-1)) * C (embed m s secondQuad)))
    (n : ℕ) (hn : n ≤ 15) :
    expCoeff (exponentPolynomial m s) n = (Q n).eval (1/2) := by
  have he := centered_solution_unique m s Q (solution m s)
    (h0.trans (solution_zero m s).symm)
    (fun j hj => (hb j hj).trans (solution_boundary m s j hj).symm)
    hQ (solution_derivative m s) n hn
  rw [he]
  exact exponential_matches_solution m s n hn

/-- The coordinate basis used in the recurrence is the physical pure midpoint
quaternion. -/
theorem embed_first (m s : Vec3) :
    embed m s firstQuad = fohQ 0 (m 0) (m 1) (m 2) := by
  ext <;> simp [embed, firstQuad, fohQ]

/-- The second coordinate basis vector is the physical pure slope quaternion. -/
theorem embed_second (m s : Vec3) :
    embed m s secondQuad = fohQ 0 (s 0) (s 1) (s 2) := by
  ext <;> simp [embed, secondQuad, fohQ]

end DegreeFifteen
end GNC.Magnus
