import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import GNC.Control.IntegralTube

/-! # Transported error certificate on a four dimensional Euclidean state

A local reference transition candidate `Ψ` and a symplectic partner `H`
transport an error vector `e` obeying `e' = A e + n`. The exact kernel
identity

  `e t = Ψ t (e 0 + ∫₀ᵗ ((H' + H A) e + H n)) + (1 - Ψ t H t) e t`

converts the differential error into an integral one, and the residual
`(1 - Ψ t H t)` measures how far the candidate transition is from the true
one. Bounding the integrand by Frobenius matrix norms and closing the tube
by a first exit argument yields a self contained bound on `‖e t‖` in which
the size of the transition matrix `Ψ` multiplies the initial error and the
accumulated forcing, but never inflates the residual. Everything is stated
on `E := EuclideanSpace ℝ (Fin 4)` with `Matrix (Fin 4) (Fin 4) ℝ` acting
through `Matrix.toEuclideanCLM`, so the ambient norm is the Euclidean one
and the operator action admits the Frobenius bound `‖M v‖ ≤ ‖M‖_F ‖v‖`.
No gravity or specific dynamics enter here. -/

open Matrix Set Finset MeasureTheory intervalIntegral
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace GNC.Transported

/-- The four dimensional Euclidean state space. -/
abbrev E := EuclideanSpace ℝ (Fin 4)

/-- The action of a matrix on a Euclidean vector, realized through the star
algebra equivalence `Matrix.toEuclideanCLM`, so that the ambient norm is the
Euclidean one and the Frobenius bound below holds. -/
abbrev act (M : Matrix (Fin 4) (Fin 4) ℝ) (v : E) : E := toEuclideanCLM (𝕜 := ℝ) M v

/-- The matrix action packaged as an `ℝ` linear map into continuous linear
endomorphisms, used to transport differentiability of a matrix curve. -/
def actL : Matrix (Fin 4) (Fin 4) ℝ →ₗ[ℝ] (E →L[ℝ] E) where
  toFun M := toEuclideanCLM (𝕜 := ℝ) M
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _

@[simp] theorem act_one (v : E) : act 1 v = v := by
  simp only [act, map_one, ContinuousLinearMap.one_apply]

theorem act_mul (M N : Matrix (Fin 4) (Fin 4) ℝ) (v : E) :
    act (M * N) v = act M (act N v) := by
  simp only [act, map_mul, ContinuousLinearMap.mul_apply]

theorem act_add (M N : Matrix (Fin 4) (Fin 4) ℝ) (v : E) :
    act (M + N) v = act M v + act N v := by
  simp only [act, map_add, ContinuousLinearMap.add_apply]

theorem act_sub (M N : Matrix (Fin 4) (Fin 4) ℝ) (v : E) :
    act (M - N) v = act M v - act N v := by
  simp only [act, map_sub, ContinuousLinearMap.sub_apply]

theorem act_vec_add (M : Matrix (Fin 4) (Fin 4) ℝ) (v w : E) :
    act M (v + w) = act M v + act M w := map_add _ _ _

theorem act_vec_sum {ι : Type*} (M : Matrix (Fin 4) (Fin 4) ℝ) (s : Finset ι) (f : ι → E) :
    act M (∑ i ∈ s, f i) = ∑ i ∈ s, act M (f i) := map_sum _ _ _

/-- The `i`-th coordinate of a matrix action is the corresponding matrix row
dotted with the vector. -/
theorem act_component (M : Matrix (Fin 4) (Fin 4) ℝ) (v : E) (i : Fin 4) :
    (act M v) i = ∑ j, M i j * v j := by
  have h : (act M v) = (M *ᵥ (v : Fin 4 → ℝ)) := ofLp_toEuclideanCLM M v
  rw [h]; rfl

/-! ## Frobenius bounds -/

/-- The Frobenius norm of a matrix. -/
def frob (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, (M i j) ^ 2)

/-- The Frobenius norm restricted to the velocity columns `2, 3`. -/
def frobVel (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j ∈ ({2, 3} : Finset (Fin 4)), (M i j) ^ 2)

theorem frob_nonneg (M : Matrix (Fin 4) (Fin 4) ℝ) : 0 ≤ frob M := Real.sqrt_nonneg _

theorem frobVel_nonneg (M : Matrix (Fin 4) (Fin 4) ℝ) : 0 ≤ frobVel M := Real.sqrt_nonneg _

/-- The Frobenius operator bound, via the finite Cauchy-Schwarz inequality:
`‖M v‖ ≤ ‖M‖_F ‖v‖`. -/
theorem mulVec_norm_le_frobenius (M : Matrix (Fin 4) (Fin 4) ℝ) (v : E) :
    ‖act M v‖ ≤ frob M * ‖v‖ := by
  rw [EuclideanSpace.norm_eq, frob, EuclideanSpace.norm_eq, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖(act M v) i‖ ^ 2 = ∑ i, (∑ j, M i j * v j) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [act_component, Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ i, (∑ j, (M i j) ^ 2) * ∑ j, (v j) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => M i j) (fun j => v j)
    _ = (∑ i, ∑ j, (M i j) ^ 2) * ∑ j, (v j) ^ 2 := by rw [Finset.sum_mul]
    _ = (∑ i, ∑ j, M i j ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]

/-- The velocity column Frobenius bound: if the position coordinates of `v`
vanish then `‖M v‖` is controlled by the velocity columns of `M` alone. -/
theorem mulVec_norm_le_frobeniusVel (M : Matrix (Fin 4) (Fin 4) ℝ) (v : E)
    (h0 : v 0 = 0) (h1 : v 1 = 0) : ‖act M v‖ ≤ frobVel M * ‖v‖ := by
  rw [EuclideanSpace.norm_eq, frobVel, EuclideanSpace.norm_eq, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hrestrict : ∀ i : Fin 4,
      (∑ j, M i j * v j) = ∑ j ∈ ({2, 3} : Finset (Fin 4)), M i j * v j := by
    intro i; symm
    refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
    fin_cases j <;> simp_all
  have hvsum : ∑ i, ‖v i‖ ^ 2 = ∑ i, (v i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_; rw [Real.norm_eq_abs, sq_abs]
  calc ∑ i, ‖(act M v) i‖ ^ 2
      = ∑ i, (∑ j ∈ ({2, 3} : Finset (Fin 4)), M i j * v j) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [act_component, Real.norm_eq_abs, sq_abs, hrestrict]
    _ ≤ ∑ i, (∑ j ∈ ({2, 3} : Finset (Fin 4)), (M i j) ^ 2) *
          (∑ j ∈ ({2, 3} : Finset (Fin 4)), (v j) ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.sum_mul_sq_le_sq_mul_sq _ (fun j => M i j) (fun j => v j)
    _ = (∑ i, ∑ j ∈ ({2, 3} : Finset (Fin 4)), (M i j) ^ 2) *
          (∑ j ∈ ({2, 3} : Finset (Fin 4)), (v j) ^ 2) := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j ∈ ({2, 3} : Finset (Fin 4)), M i j ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
        rw [hvsum]
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => by positivity)) (by positivity)

/-! ## Row block projections

Position errors live in rows `0, 1` and velocity errors in rows `2, 3`. The
row restricted Frobenius norm bounds the corresponding block of a matrix
action, giving separate position and velocity bounds. The projection onto a
row set is realized by left multiplication with the `0, 1` diagonal indicator,
so it composes with the matrix action. -/

/-- The Frobenius norm restricted to a set of rows. -/
def frobRows (R : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Real.sqrt (∑ i ∈ R, ∑ j, (M i j) ^ 2)

theorem frobRows_nonneg (R : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    0 ≤ frobRows R M := Real.sqrt_nonneg _

/-- The `0, 1` indicator diagonal, whose left action zeros all rows outside
`R`. -/
def diagRows (R : Finset (Fin 4)) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => if i ∈ R then (1 : ℝ) else 0)

/-- The projection of a vector onto the rows in `R`. -/
def projRows (R : Finset (Fin 4)) (v : E) : E := act (diagRows R) v

theorem frob_diagRows_mul (R : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    frob (diagRows R * M) = frobRows R M := by
  have hcomp : ∀ i j, (diagRows R * M) i j = if i ∈ R then M i j else 0 := by
    intro i j; rw [diagRows, Matrix.diagonal_mul]; by_cases h : i ∈ R <;> simp [h]
  have hsum : ∑ i, ∑ j, ((diagRows R * M) i j) ^ 2 = ∑ i ∈ R, ∑ j, (M i j) ^ 2 := by
    calc ∑ i, ∑ j, ((diagRows R * M) i j) ^ 2
        = ∑ i, (if i ∈ R then ∑ j, (M i j) ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hcomp]; by_cases h : i ∈ R <;> simp [h]
      _ = ∑ i ∈ R, ∑ j, (M i j) ^ 2 := by rw [← Finset.sum_filter]; congr 1; ext i; simp
  rw [frob, frobRows, hsum]

/-- Row block Frobenius bound: the rows in `R` of a matrix action are bounded
by the row restricted Frobenius norm. -/
theorem projRows_act_le (R : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) (v : E) :
    ‖projRows R (act M v)‖ ≤ frobRows R M * ‖v‖ := by
  rw [projRows, ← act_mul]
  calc ‖act (diagRows R * M) v‖ ≤ frob (diagRows R * M) * ‖v‖ := mulVec_norm_le_frobenius _ _
    _ = frobRows R M * ‖v‖ := by rw [frob_diagRows_mul]

/-- The Frobenius norm restricted to rows `R` and velocity columns `{2, 3}`. -/
def frobRowsVel (R : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Real.sqrt (∑ i ∈ R, ∑ j ∈ ({2, 3} : Finset (Fin 4)), (M i j) ^ 2)

theorem frobRowsVel_nonneg (R : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    0 ≤ frobRowsVel R M := Real.sqrt_nonneg _

theorem frobVel_diagRows_mul (R : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    frobVel (diagRows R * M) = frobRowsVel R M := by
  have hcomp : ∀ i j, (diagRows R * M) i j = if i ∈ R then M i j else 0 := by
    intro i j; rw [diagRows, Matrix.diagonal_mul]; by_cases h : i ∈ R <;> simp [h]
  have hsum : ∑ i, ∑ j ∈ ({2, 3} : Finset (Fin 4)), ((diagRows R * M) i j) ^ 2
      = ∑ i ∈ R, ∑ j ∈ ({2, 3} : Finset (Fin 4)), (M i j) ^ 2 := by
    calc ∑ i, ∑ j ∈ ({2, 3} : Finset (Fin 4)), ((diagRows R * M) i j) ^ 2
        = ∑ i, (if i ∈ R then ∑ j ∈ ({2, 3} : Finset (Fin 4)), (M i j) ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hcomp]; by_cases h : i ∈ R <;> simp [h]
      _ = ∑ i ∈ R, ∑ j ∈ ({2, 3} : Finset (Fin 4)), (M i j) ^ 2 := by
          rw [← Finset.sum_filter]; congr 1; ext i; simp
  rw [frobVel, frobRowsVel, hsum]

/-- Row and velocity column block bound: if the position coordinates of `v`
vanish, the rows in `R` of the action are controlled by the row and velocity
column restricted Frobenius norm. -/
theorem projRows_act_le_vel (R : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) (v : E)
    (h0 : v 0 = 0) (h1 : v 1 = 0) : ‖projRows R (act M v)‖ ≤ frobRowsVel R M * ‖v‖ := by
  rw [projRows, ← act_mul]
  calc ‖act (diagRows R * M) v‖ ≤ frobVel (diagRows R * M) * ‖v‖ :=
        mulVec_norm_le_frobeniusVel _ _ h0 h1
    _ = frobRowsVel R M * ‖v‖ := by rw [frobVel_diagRows_mul]

theorem projRows_vadd (R : Finset (Fin 4)) (v w : E) :
    projRows R (v + w) = projRows R v + projRows R w := act_vec_add _ _ _

theorem projRows_vsum {ι : Type*} (R : Finset (Fin 4)) (s : Finset ι) (f : ι → E) :
    projRows R (∑ i ∈ s, f i) = ∑ i ∈ s, projRows R (f i) := act_vec_sum _ _ _

/-! ## Differentiability transport -/

/-- Differentiability of a matrix curve is transported to its Euclidean
action operator. -/
theorem clm_hasDerivAt {H : ℝ → Matrix (Fin 4) (Fin 4) ℝ}
    {H' : Matrix (Fin 4) (Fin 4) ℝ} {s : ℝ} (h : HasDerivAt H H' s) :
    HasDerivAt (fun s => (toEuclideanCLM (𝕜 := ℝ) (H s) : E →L[ℝ] E))
      (toEuclideanCLM (𝕜 := ℝ) H') s :=
  actL.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s h

/-! ## The step kernel -/

/-- The transported integrand `(H' + H A) e + H n`. -/
def drift (H A H' : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (e n : ℝ → E) (s : ℝ) : E :=
  act (H' s + H s * A s) (e s) + act (H s) (n s)

/-- The exact step kernel identity. With `H 0 = 1`, integrating the
derivative of `s ↦ H s (e s)` and applying `Ψ t` gives the error at time `t`
as the transported initial error plus the transported accumulated forcing,
corrected by the transition residual `(1 - Ψ t H t)`. -/
theorem step_identity (Ψ H A H' : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (e n : ℝ → E) {h : ℝ}
    (hH0 : H 0 = 1)
    (hHd : ∀ s ∈ uIcc (0 : ℝ) h, HasDerivAt H (H' s) s)
    (hed : ∀ s ∈ uIcc (0 : ℝ) h, HasDerivAt e (act (A s) (e s) + n s) s)
    (hcont : Continuous (drift H A H' e n))
    {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) h) :
    e t = act (Ψ t) (e 0 + ∫ s in (0 : ℝ)..t, drift H A H' e n s)
      + act (1 - Ψ t * H t) (e t) := by
  set φ : ℝ → E := fun s => act (H s) (e s) with hφdef
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) h := uIcc_subset_uIcc left_mem_uIcc ht
  have hφderiv : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt φ (drift H A H' e n s) s := by
    intro s hs
    have hd := (clm_hasDerivAt (hHd s (hsub hs))).clm_apply (hed s (hsub hs))
    refine hd.congr_deriv ?_
    simp only [drift, act, map_add, map_mul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply]
    abel
  have hint : IntervalIntegrable (drift H A H' e n) volume 0 t :=
    hcont.intervalIntegrable 0 t
  have hFTC : ∫ s in (0 : ℝ)..t, drift H A H' e n s = φ t - φ 0 :=
    integral_eq_sub_of_hasDerivAt hφderiv hint
  have hφ0 : φ 0 = e 0 := by simp only [hφdef, act, hH0, map_one]; rfl
  have hφt : φ t = e 0 + ∫ s in (0 : ℝ)..t, drift H A H' e n s := by
    rw [hFTC, hφ0]; abel
  have hdecomp : e t = act (Ψ t * H t) (e t) + act (1 - Ψ t * H t) (e t) := by
    simp only [act, ← ContinuousLinearMap.add_apply, ← map_add]
    rw [add_sub_cancel, map_one]; rfl
  have hfirst : act (Ψ t * H t) (e t)
      = act (Ψ t) (e 0 + ∫ s in (0 : ℝ)..t, drift H A H' e n s) := by
    rw [← hφt]
    simp only [act, map_mul, ContinuousLinearMap.mul_apply]
    rfl
  conv_lhs => rw [hdecomp]
  rw [hfirst]

/-- Pointwise bound on the transported integrand inside the tube. The
candidate gradient `Â` splits `A` into a part that shares the polynomial
transition with `H` and a residual `A - Â` supported on the velocity rows,
so `H (A - Â) e` and `H n` are both controlled by the velocity columns of
`H`. -/
theorem drift_norm_le (H A Â H' : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (e n : ℝ → E)
    {M K_R F kR kV εA : ℝ} {s : ℝ}
    (hAp0 : ∀ j, (A s - Â s) 0 j = 0) (hAp1 : ∀ j, (A s - Â s) 1 j = 0)
    (hn0 : (n s) 0 = 0) (hn1 : (n s) 1 = 0)
    (hkR : frob (H' s + H s * Â s) ≤ kR) (hkV : frobVel (H s) ≤ kV)
    (hεA : frob (A s - Â s) ≤ εA)
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K_R)
    (heM : ‖e s‖ ≤ M) (hnb : ‖n s‖ ≤ K_R * ‖e s‖ ^ 2 + F) :
    ‖drift H A H' e n s‖ ≤ kV * (K_R * M ^ 2 + F + εA * M) + kR * M := by
  have hkR0 : 0 ≤ kR := le_trans (frob_nonneg _) hkR
  have hkV0 : 0 ≤ kV := le_trans (frobVel_nonneg _) hkV
  have hεA0 : 0 ≤ εA := le_trans (frob_nonneg _) hεA
  have hdecomp : drift H A H' e n s
      = act (H' s + H s * Â s) (e s) + act (H s) (act (A s - Â s) (e s))
        + act (H s) (n s) := by
    unfold drift
    rw [show H' s + H s * A s = (H' s + H s * Â s) + H s * (A s - Â s) by
      rw [mul_sub]; abel, act_add, act_mul]
  have hpz0 : (act (A s - Â s) (e s)) 0 = 0 := by
    rw [act_component]; simp only [hAp0, zero_mul, Finset.sum_const_zero]
  have hpz1 : (act (A s - Â s) (e s)) 1 = 0 := by
    rw [act_component]; simp only [hAp1, zero_mul, Finset.sum_const_zero]
  -- term 1
  have ht1 : ‖act (H' s + H s * Â s) (e s)‖ ≤ kR * M :=
    (mulVec_norm_le_frobenius _ _).trans (by
      calc frob (H' s + H s * Â s) * ‖e s‖ ≤ kR * ‖e s‖ :=
              mul_le_mul_of_nonneg_right hkR (norm_nonneg _)
        _ ≤ kR * M := mul_le_mul_of_nonneg_left heM hkR0)
  -- term 2
  have hAe : ‖act (A s - Â s) (e s)‖ ≤ εA * M :=
    (mulVec_norm_le_frobenius _ _).trans (by
      calc frob (A s - Â s) * ‖e s‖ ≤ εA * ‖e s‖ :=
              mul_le_mul_of_nonneg_right hεA (norm_nonneg _)
        _ ≤ εA * M := mul_le_mul_of_nonneg_left heM hεA0)
  have ht2 : ‖act (H s) (act (A s - Â s) (e s))‖ ≤ kV * (εA * M) :=
    (mulVec_norm_le_frobeniusVel _ _ hpz0 hpz1).trans (by
      calc frobVel (H s) * ‖act (A s - Â s) (e s)‖ ≤ kV * ‖act (A s - Â s) (e s)‖ :=
              mul_le_mul_of_nonneg_right hkV (norm_nonneg _)
        _ ≤ kV * (εA * M) := mul_le_mul_of_nonneg_left hAe hkV0)
  -- term 3
  have hnM : ‖n s‖ ≤ K_R * M ^ 2 + F := by
    have : ‖e s‖ ^ 2 ≤ M ^ 2 := by
      have := sq_le_sq' (by linarith [norm_nonneg (e s)]) heM; simpa using this
    nlinarith [hnb]
  have ht3 : ‖act (H s) (n s)‖ ≤ kV * (K_R * M ^ 2 + F) :=
    (mulVec_norm_le_frobeniusVel _ _ hn0 hn1).trans (by
      calc frobVel (H s) * ‖n s‖ ≤ kV * ‖n s‖ :=
              mul_le_mul_of_nonneg_right hkV (norm_nonneg _)
        _ ≤ kV * (K_R * M ^ 2 + F) := mul_le_mul_of_nonneg_left hnM hkV0)
  rw [hdecomp]
  calc ‖act (H' s + H s * Â s) (e s) + act (H s) (act (A s - Â s) (e s)) + act (H s) (n s)‖
      ≤ ‖act (H' s + H s * Â s) (e s) + act (H s) (act (A s - Â s) (e s))‖ + ‖act (H s) (n s)‖ :=
        norm_add_le _ _
    _ ≤ (‖act (H' s + H s * Â s) (e s)‖ + ‖act (H s) (act (A s - Â s) (e s))‖) + ‖act (H s) (n s)‖ :=
        by gcongr; exact norm_add_le _ _
    _ ≤ (kR * M + kV * (εA * M)) + kV * (K_R * M ^ 2 + F) := by gcongr
    _ = kV * (K_R * M ^ 2 + F + εA * M) + kR * M := by ring

/-- Prefixed drift bound. With a constant left factor `G` (a composed
transition) applied to the transported integrand, the velocity columns of the
composed kernels `G H` and `G (H' + H Â)` carry the bound, since both the
forcing `n` and the gradient defect `(A - Â) e` have zero position components.
This is the composition tight version of `drift_norm_le`: it never separates
`‖G‖` from the velocity column norm. -/
theorem prefixed_drift_norm_le (G : Matrix (Fin 4) (Fin 4) ℝ)
    (H A Â H' : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (e n : ℝ → E)
    {M K_R F kR kV εA : ℝ} {s : ℝ}
    (hAp0 : ∀ j, (A s - Â s) 0 j = 0) (hAp1 : ∀ j, (A s - Â s) 1 j = 0)
    (hn0 : (n s) 0 = 0) (hn1 : (n s) 1 = 0)
    (hkR : frob (G * (H' s + H s * Â s)) ≤ kR) (hkV : frobVel (G * H s) ≤ kV)
    (hεA : frob (A s - Â s) ≤ εA)
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K_R)
    (heM : ‖e s‖ ≤ M) (hnb : ‖n s‖ ≤ K_R * ‖e s‖ ^ 2 + F) :
    ‖act G (drift H A H' e n s)‖ ≤ kV * (K_R * M ^ 2 + F + εA * M) + kR * M := by
  have hkR0 : 0 ≤ kR := le_trans (frob_nonneg _) hkR
  have hkV0 : 0 ≤ kV := le_trans (frobVel_nonneg _) hkV
  have hεA0 : 0 ≤ εA := le_trans (frob_nonneg _) hεA
  have hdecomp : act G (drift H A H' e n s)
      = act (G * (H' s + H s * Â s)) (e s) + act (G * H s) (act (A s - Â s) (e s))
        + act (G * H s) (n s) := by
    unfold drift
    rw [act_vec_add, ← act_mul, ← act_mul,
      show G * (H' s + H s * A s) = G * (H' s + H s * Â s) + G * H s * (A s - Â s) by
        noncomm_ring,
      act_add,
      show act (G * H s * (A s - Â s)) (e s) = act (G * H s) (act (A s - Â s) (e s)) from
        act_mul _ _ _]
  have hpz0 : (act (A s - Â s) (e s)) 0 = 0 := by
    rw [act_component]; simp only [hAp0, zero_mul, Finset.sum_const_zero]
  have hpz1 : (act (A s - Â s) (e s)) 1 = 0 := by
    rw [act_component]; simp only [hAp1, zero_mul, Finset.sum_const_zero]
  have ht1 : ‖act (G * (H' s + H s * Â s)) (e s)‖ ≤ kR * M :=
    (mulVec_norm_le_frobenius _ _).trans (by
      calc frob (G * (H' s + H s * Â s)) * ‖e s‖ ≤ kR * ‖e s‖ :=
              mul_le_mul_of_nonneg_right hkR (norm_nonneg _)
        _ ≤ kR * M := mul_le_mul_of_nonneg_left heM hkR0)
  have hAe : ‖act (A s - Â s) (e s)‖ ≤ εA * M :=
    (mulVec_norm_le_frobenius _ _).trans (by
      calc frob (A s - Â s) * ‖e s‖ ≤ εA * ‖e s‖ :=
              mul_le_mul_of_nonneg_right hεA (norm_nonneg _)
        _ ≤ εA * M := mul_le_mul_of_nonneg_left heM hεA0)
  have ht2 : ‖act (G * H s) (act (A s - Â s) (e s))‖ ≤ kV * (εA * M) :=
    (mulVec_norm_le_frobeniusVel _ _ hpz0 hpz1).trans (by
      calc frobVel (G * H s) * ‖act (A s - Â s) (e s)‖ ≤ kV * ‖act (A s - Â s) (e s)‖ :=
              mul_le_mul_of_nonneg_right hkV (norm_nonneg _)
        _ ≤ kV * (εA * M) := mul_le_mul_of_nonneg_left hAe hkV0)
  have hnM : ‖n s‖ ≤ K_R * M ^ 2 + F := by
    have hsq : ‖e s‖ ^ 2 ≤ M ^ 2 := by
      have := sq_le_sq' (by linarith [norm_nonneg (e s)]) heM; simpa using this
    nlinarith [hnb]
  have ht3 : ‖act (G * H s) (n s)‖ ≤ kV * (K_R * M ^ 2 + F) :=
    (mulVec_norm_le_frobeniusVel _ _ hn0 hn1).trans (by
      calc frobVel (G * H s) * ‖n s‖ ≤ kV * ‖n s‖ :=
              mul_le_mul_of_nonneg_right hkV (norm_nonneg _)
        _ ≤ kV * (K_R * M ^ 2 + F) := mul_le_mul_of_nonneg_left hnM hkV0)
  rw [hdecomp]
  calc ‖act (G * (H' s + H s * Â s)) (e s) + act (G * H s) (act (A s - Â s) (e s))
          + act (G * H s) (n s)‖
      ≤ ‖act (G * (H' s + H s * Â s)) (e s) + act (G * H s) (act (A s - Â s) (e s))‖
          + ‖act (G * H s) (n s)‖ := norm_add_le _ _
    _ ≤ (‖act (G * (H' s + H s * Â s)) (e s)‖ + ‖act (G * H s) (act (A s - Â s) (e s))‖)
          + ‖act (G * H s) (n s)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (kR * M + kV * (εA * M)) + kV * (K_R * M ^ 2 + F) := by gcongr
    _ = kV * (K_R * M ^ 2 + F + εA * M) + kR * M := by ring

/-- The composed transition applied to one step's accumulated forcing.
Commuting the constant left factor `G` with the interval integral and using
the prefixed drift bound gives a bound proportional to the step length in
which the velocity column norms of the composed kernels appear. -/
theorem prefixed_int_norm_le (G : Matrix (Fin 4) (Fin 4) ℝ)
    (H A Â H' : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (e n : ℝ → E)
    {hstep M K_R F kR kV εA : ℝ}
    (hstep0 : 0 ≤ hstep) (hcont : Continuous (drift H A H' e n))
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K_R)
    (hAp0 : ∀ s j, (A s - Â s) 0 j = 0) (hAp1 : ∀ s j, (A s - Â s) 1 j = 0)
    (hn0 : ∀ s, (n s) 0 = 0) (hn1 : ∀ s, (n s) 1 = 0)
    (hkR : ∀ s ∈ Icc (0 : ℝ) hstep, frob (G * (H' s + H s * Â s)) ≤ kR)
    (hkV : ∀ s ∈ Icc (0 : ℝ) hstep, frobVel (G * H s) ≤ kV)
    (hεA : ∀ s ∈ Icc (0 : ℝ) hstep, frob (A s - Â s) ≤ εA)
    (hetube : ∀ s ∈ Icc (0 : ℝ) hstep, ‖e s‖ ≤ M)
    (hnb : ∀ s ∈ Icc (0 : ℝ) hstep, ‖e s‖ ≤ M → ‖n s‖ ≤ K_R * ‖e s‖ ^ 2 + F) :
    ‖act G (∫ s in (0 : ℝ)..hstep, drift H A H' e n s)‖
      ≤ (kV * (K_R * M ^ 2 + F + εA * M) + kR * M) * hstep := by
  have hint : IntervalIntegrable (drift H A H' e n) volume 0 hstep :=
    hcont.intervalIntegrable 0 hstep
  have hcomm : act G (∫ s in (0 : ℝ)..hstep, drift H A H' e n s)
      = ∫ s in (0 : ℝ)..hstep, act G (drift H A H' e n s) :=
    ((toEuclideanCLM (𝕜 := ℝ) G).intervalIntegral_comp_comm hint).symm
  rw [hcomm]
  have hpt : ∀ s ∈ Set.uIoc (0 : ℝ) hstep,
      ‖act G (drift H A H' e n s)‖ ≤ kV * (K_R * M ^ 2 + F + εA * M) + kR * M := by
    intro s hs
    rw [uIoc_of_le hstep0] at hs
    have hsIcc : s ∈ Icc (0 : ℝ) hstep := ⟨hs.1.le, hs.2⟩
    exact prefixed_drift_norm_le G H A Â H' e n (hAp0 s) (hAp1 s) (hn0 s) (hn1 s)
      (hkR s hsIcc) (hkV s hsIcc) (hεA s hsIcc) hM0 hK0 (hetube s hsIcc)
      (hnb s hsIcc (hetube s hsIcc))
  have h := norm_integral_le_of_norm_le_const hpt
  rwa [sub_zero, abs_of_nonneg hstep0] at h

/-- The step bound. Inside a tube of radius `M`, the transported error at
time `t` obeys `(1 - εI) ‖e t‖ ≤ ψ (‖e 0‖ + t (kV (K_R M² + F + εA M) + kR M))`,
where `εI` bounds the transition residual, `ψ` the transition norm, `kR` and
`kV` the drift and velocity column norms of `H`, and `εA` the gradient
candidate error. The size `ψ` of the transition multiplies only the initial
error and the accumulated forcing. -/
theorem step_bound (Ψ H A Â H' : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (e n : ℝ → E)
    {h M K_R F εI ψ kR kV εA : ℝ}
    (hH0 : H 0 = 1)
    (hHd : ∀ s ∈ Icc (0 : ℝ) h, HasDerivAt H (H' s) s)
    (hed : ∀ s ∈ Icc (0 : ℝ) h, HasDerivAt e (act (A s) (e s) + n s) s)
    (hcont : Continuous (drift H A H' e n))
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K_R)
    (hAp0 : ∀ s j, (A s - Â s) 0 j = 0) (hAp1 : ∀ s j, (A s - Â s) 1 j = 0)
    (hn0 : ∀ s, (n s) 0 = 0) (hn1 : ∀ s, (n s) 1 = 0)
    (hkR : ∀ s ∈ Icc (0 : ℝ) h, frob (H' s + H s * Â s) ≤ kR)
    (hkV : ∀ s ∈ Icc (0 : ℝ) h, frobVel (H s) ≤ kV)
    (hεA : ∀ s ∈ Icc (0 : ℝ) h, frob (A s - Â s) ≤ εA)
    (hnb : ∀ s ∈ Icc (0 : ℝ) h, ‖e s‖ ≤ M → ‖n s‖ ≤ K_R * ‖e s‖ ^ 2 + F)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) h)
    (hεI : frob (1 - Ψ t * H t) ≤ εI) (hψ : frob (Ψ t) ≤ ψ)
    (hetube : ∀ s ∈ Icc (0 : ℝ) t, ‖e s‖ ≤ M) :
    (1 - εI) * ‖e t‖ ≤ ψ * (‖e 0‖ + t * (kV * (K_R * M ^ 2 + F + εA * M) + kR * M)) := by
  obtain ⟨ht0, hth⟩ := ht
  have hψ0 : 0 ≤ ψ := le_trans (frob_nonneg _) hψ
  set D : ℝ := kV * (K_R * M ^ 2 + F + εA * M) + kR * M with hD
  -- pointwise integrand bound on the interval
  have hdb : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖drift H A H' e n s‖ ≤ D := by
    intro s hs
    rw [uIoc_of_le ht0] at hs
    have hsIcc : s ∈ Icc (0 : ℝ) h := ⟨hs.1.le, hs.2.trans hth⟩
    exact drift_norm_le H A Â H' e n (hAp0 s) (hAp1 s) (hn0 s) (hn1 s)
      (hkR s hsIcc) (hkV s hsIcc) (hεA s hsIcc) hM0 hK0 (hetube s ⟨hs.1.le, hs.2⟩)
      (hnb s hsIcc (hetube s ⟨hs.1.le, hs.2⟩))
  have hintbound : ‖∫ s in (0 : ℝ)..t, drift H A H' e n s‖ ≤ t * D := by
    have h := norm_integral_le_of_norm_le_const hdb
    rwa [sub_zero, abs_of_nonneg ht0, mul_comm] at h
  -- kernel identity
  have hid := step_identity Ψ H A H' e n hH0
    (fun s hs => hHd s (by rwa [uIcc_of_le (ht0.trans hth)] at hs))
    (fun s hs => hed s (by rwa [uIcc_of_le (ht0.trans hth)] at hs)) hcont
    (t := t) (Icc_subset_uIcc ⟨ht0, hth⟩)
  -- transported initial term
  have h1 : ‖act (Ψ t) (e 0 + ∫ s in (0 : ℝ)..t, drift H A H' e n s)‖
      ≤ ψ * (‖e 0‖ + t * D) :=
    (mulVec_norm_le_frobenius _ _).trans (by
      calc frob (Ψ t) * ‖e 0 + ∫ s in (0 : ℝ)..t, drift H A H' e n s‖
            ≤ ψ * ‖e 0 + ∫ s in (0 : ℝ)..t, drift H A H' e n s‖ :=
              mul_le_mul_of_nonneg_right hψ (norm_nonneg _)
        _ ≤ ψ * (‖e 0‖ + t * D) := by
              refine mul_le_mul_of_nonneg_left ?_ hψ0
              exact (norm_add_le _ _).trans (by linarith [hintbound]))
  -- residual term
  have h2 : ‖act (1 - Ψ t * H t) (e t)‖ ≤ εI * ‖e t‖ :=
    (mulVec_norm_le_frobenius _ _).trans (mul_le_mul_of_nonneg_right hεI (norm_nonneg _))
  have hnorm : ‖e t‖ ≤ ψ * (‖e 0‖ + t * D) + εI * ‖e t‖ := by
    calc ‖e t‖ = ‖act (Ψ t) (e 0 + ∫ s in (0 : ℝ)..t, drift H A H' e n s)
                  + act (1 - Ψ t * H t) (e t)‖ := by rw [← hid]
      _ ≤ ‖act (Ψ t) (e 0 + ∫ s in (0 : ℝ)..t, drift H A H' e n s)‖
            + ‖act (1 - Ψ t * H t) (e t)‖ := norm_add_le _ _
      _ ≤ ψ * (‖e 0‖ + t * D) + εI * ‖e t‖ := add_le_add h1 h2
  linarith [hnorm]

/-- First exit tube. If the transition residual is a contraction (`εI < 1`),
the initial error is inside the tube, and the closed loop gain
`ψ (‖e 0‖ + h (kV (K_R M² + F + εA M) + kR M))` stays below `(1 - εI) M`, then
the error never leaves the tube of radius `M` on `[0, h]`. -/
theorem step_tube (Ψ H A Â H' : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (e n : ℝ → E)
    {h M K_R F εI ψ kR kV εA : ℝ}
    (hH0 : H 0 = 1)
    (hHd : ∀ s ∈ Icc (0 : ℝ) h, HasDerivAt H (H' s) s)
    (hed : ∀ s ∈ Icc (0 : ℝ) h, HasDerivAt e (act (A s) (e s) + n s) s)
    (hec : Continuous e) (hcont : Continuous (drift H A H' e n))
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K_R) (hF0 : 0 ≤ F) (hεI1 : εI < 1)
    (hAp0 : ∀ s j, (A s - Â s) 0 j = 0) (hAp1 : ∀ s j, (A s - Â s) 1 j = 0)
    (hn0 : ∀ s, (n s) 0 = 0) (hn1 : ∀ s, (n s) 1 = 0)
    (hεI : ∀ t ∈ Icc (0 : ℝ) h, frob (1 - Ψ t * H t) ≤ εI)
    (hψ : ∀ t ∈ Icc (0 : ℝ) h, frob (Ψ t) ≤ ψ)
    (hkR : ∀ s ∈ Icc (0 : ℝ) h, frob (H' s + H s * Â s) ≤ kR)
    (hkV : ∀ s ∈ Icc (0 : ℝ) h, frobVel (H s) ≤ kV)
    (hεA : ∀ s ∈ Icc (0 : ℝ) h, frob (A s - Â s) ≤ εA)
    (hnb : ∀ s ∈ Icc (0 : ℝ) h, ‖e s‖ ≤ M → ‖n s‖ ≤ K_R * ‖e s‖ ^ 2 + F)
    (hinit : ‖e 0‖ < M)
    (hclose : ψ * (‖e 0‖ + h * (kV * (K_R * M ^ 2 + F + εA * M) + kR * M)) < (1 - εI) * M) :
    ∀ t ∈ Icc (0 : ℝ) h, ‖e t‖ < M := by
  have hpos : 0 < 1 - εI := by linarith
  set D : ℝ := kV * (K_R * M ^ 2 + F + εA * M) + kR * M with hD
  apply IntegralTube.prefix_closure hec.norm hinit
  intro t ht hprefix
  have hkV0 : 0 ≤ kV := le_trans (frobVel_nonneg _) (hkV t ht)
  have hkR0 : 0 ≤ kR := le_trans (frob_nonneg _) (hkR t ht)
  have hεA0 : 0 ≤ εA := le_trans (frob_nonneg _) (hεA t ht)
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hb := step_bound Ψ H A Â H' e n hH0 hHd hed hcont hM0 hK0 hAp0 hAp1 hn0 hn1
    hkR hkV hεA hnb ht (hεI t ht) (hψ t ht) hprefix
  have hmono : ψ * (‖e 0‖ + t * D) ≤ ψ * (‖e 0‖ + h * D) := by
    have hψ0 : 0 ≤ ψ := le_trans (frob_nonneg _) (hψ t ht)
    gcongr
    exact ht.2
  have : (1 - εI) * ‖e t‖ < (1 - εI) * M := by
    calc (1 - εI) * ‖e t‖ ≤ ψ * (‖e 0‖ + t * D) := hb
      _ ≤ ψ * (‖e 0‖ + h * D) := hmono
      _ < (1 - εI) * M := hclose
  exact lt_of_mul_lt_mul_left this hpos.le

/-! ## Composition over a chain of local steps

The steps use independent local transition candidates, so no exact junction
continuity of a global transition matrix is required. The composed transition
`stm P i j = P i * P (i-1) * ... * P j` (with `P k` the evaluated step
transition and the empty product `stm P i (i+1) = 1`) telescopes the per step
kernel identities into an exact identity at each node. -/

/-- The composed transition `stm P i j = P i * P (i-1) * ... * P j`, with
`stm P i j = 1` whenever `i < j`. -/
def stm (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) : ℕ → ℕ → Matrix (Fin 4) (Fin 4) ℝ
  | 0, j => if 0 < j then 1 else P 0
  | (i + 1), j => if i + 1 < j then 1 else P (i + 1) * stm P i j

theorem stm_succ (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (i j : ℕ) (h : j ≤ i + 1) :
    stm P (i + 1) j = P (i + 1) * stm P i j := by
  simp only [stm, if_neg (Nat.not_lt.mpr h)]

theorem stm_self_succ (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (i : ℕ) :
    stm P i (i + 1) = 1 := by
  cases i <;> simp [stm]

theorem stm_diag (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (i : ℕ) : stm P i i = P i := by
  cases i with
  | zero => simp [stm]
  | succ k => rw [stm_succ P k (k + 1) le_rfl, stm_self_succ, mul_one]

/-- The exact chain kernel identity. Telescoping the per step identities
`b i = P i (start i + c i) + slack i` (with `start 0 = e0init` and
`start (i+1) = b i`) gives the terminal error of node `i` as the composed
transition applied to the initial error, plus a node indexed sum of the
transported step inputs `c j` and residual slacks `slack j`. Here
`c j = m j + ∫_j` bundles the handoff mismatch and the accumulated step
forcing. -/
theorem chain_identity (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (e0init : E) (b c slack : ℕ → E)
    (hbase : b 0 = act (P 0) (e0init + c 0) + slack 0)
    (hsucc : ∀ i, b (i + 1) = act (P (i + 1)) (b i + c (i + 1)) + slack (i + 1)) :
    ∀ i, b i = act (stm P i 0) e0init
      + ∑ j ∈ Finset.range (i + 1),
          (act (stm P i j) (c j) + act (stm P i (j + 1)) (slack j)) := by
  intro i
  induction i with
  | zero =>
    have h1 : stm P 0 0 = P 0 := stm_diag P 0
    have h2 : stm P 0 (0 + 1) = 1 := stm_self_succ P 0
    rw [hbase, Finset.sum_range_one, h1, h2, act_vec_add, act_one]
    abel
  | succ i ih =>
    rw [hsucc i, ih]
    -- distribute act (P (i+1)) over the two vector summands and the sum on the left
    rw [act_vec_add, act_vec_add, act_vec_sum]
    -- fold the transported initial term
    rw [← act_mul, ← stm_succ P i 0 (by omega)]
    -- fold every term of the transported sum
    have hsum : (∑ j ∈ Finset.range (i + 1),
          act (P (i + 1)) (act (stm P i j) (c j) + act (stm P i (j + 1)) (slack j)))
        = ∑ j ∈ Finset.range (i + 1),
          (act (stm P (i + 1) j) (c j) + act (stm P (i + 1) (j + 1)) (slack j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [act_vec_add, ← act_mul, ← act_mul, ← stm_succ P i j (by omega),
        ← stm_succ P i (j + 1) (by omega)]
    rw [hsum]
    -- split off the final node on the right
    conv_rhs => rw [Finset.sum_range_succ]
    rw [stm_diag, stm_self_succ, act_one]
    abel

/-- The chain node bound. Taking Frobenius norms of the composed transitions
in the chain kernel identity gives a bound on the terminal error at node `i`
as the transported initial error plus a node indexed sum of the step inputs
`c j` (handoff plus accumulated forcing) and residual slacks `slack j`, each
weighted by the Frobenius norm of the corresponding composed transition. The
composition norms `kM j` and `kS j` never multiply the residual by more than
the composed transition size, so the growth is that of the true composed
transition, not a product of per step operator norms. -/
theorem chain_bound (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (e0init : E) (b c slack : ℕ → E)
    (kM kS cbar sbar : ℕ → ℝ)
    (hbase : b 0 = act (P 0) (e0init + c 0) + slack 0)
    (hsucc : ∀ i, b (i + 1) = act (P (i + 1)) (b i + c (i + 1)) + slack (i + 1))
    {i : ℕ}
    (hkM : ∀ j, j ≤ i → frob (stm P i j) ≤ kM j)
    (hkS : ∀ j, j ≤ i → frob (stm P i (j + 1)) ≤ kS j)
    (hc : ∀ j, j ≤ i → ‖c j‖ ≤ cbar j)
    (hs : ∀ j, j ≤ i → ‖slack j‖ ≤ sbar j) :
    ‖b i‖ ≤ kM 0 * ‖e0init‖
      + ∑ j ∈ Finset.range (i + 1), (kM j * cbar j + kS j * sbar j) := by
  rw [chain_identity P e0init b c slack hbase hsucc i]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (mulVec_norm_le_frobenius _ _).trans
      (mul_le_mul_of_nonneg_right (hkM 0 (Nat.zero_le _)) (norm_nonneg _))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hji : j ≤ i := by omega
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖act (stm P i j) (c j)‖ ≤ frob (stm P i j) * ‖c j‖ := mulVec_norm_le_frobenius _ _
        _ ≤ kM j * cbar j :=
            mul_le_mul (hkM j hji) (hc j hji) (norm_nonneg _)
              (le_trans (frob_nonneg _) (hkM j hji))
    · calc ‖act (stm P i (j + 1)) (slack j)‖ ≤ frob (stm P i (j + 1)) * ‖slack j‖ :=
              mulVec_norm_le_frobenius _ _
        _ ≤ kS j * sbar j :=
            mul_le_mul (hkS j hji) (hs j hji) (norm_nonneg _)
              (le_trans (frob_nonneg _) (hkS j hji))

/-- The row projected chain node bound. Projecting the chain kernel identity
onto a row block `R` (position rows `{0, 1}` or velocity rows `{2, 3}`) and
using the row restricted Frobenius norms of the composed transitions bounds
the corresponding block of the terminal error at node `i`, so position and
velocity errors receive separate bounds. -/
theorem chain_bound_rows (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (e0init : E) (b c slack : ℕ → E)
    (R : Finset (Fin 4)) (kMr kSr cbar sbar : ℕ → ℝ)
    (hbase : b 0 = act (P 0) (e0init + c 0) + slack 0)
    (hsucc : ∀ i, b (i + 1) = act (P (i + 1)) (b i + c (i + 1)) + slack (i + 1))
    {i : ℕ}
    (hkM : ∀ j, j ≤ i → frobRows R (stm P i j) ≤ kMr j)
    (hkS : ∀ j, j ≤ i → frobRows R (stm P i (j + 1)) ≤ kSr j)
    (hc : ∀ j, j ≤ i → ‖c j‖ ≤ cbar j)
    (hs : ∀ j, j ≤ i → ‖slack j‖ ≤ sbar j) :
    ‖projRows R (b i)‖ ≤ kMr 0 * ‖e0init‖
      + ∑ j ∈ Finset.range (i + 1), (kMr j * cbar j + kSr j * sbar j) := by
  rw [chain_identity P e0init b c slack hbase hsucc i, projRows, act_vec_add, act_vec_sum]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (projRows_act_le R _ _).trans
      (mul_le_mul_of_nonneg_right (hkM 0 (Nat.zero_le _)) (norm_nonneg _))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hji : j ≤ i := by omega
    rw [act_vec_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (projRows_act_le R _ _).trans
        (mul_le_mul (hkM j hji) (hc j hji) (norm_nonneg _)
          (le_trans (frobRows_nonneg _ _) (hkM j hji)))
    · exact (projRows_act_le R _ _).trans
        (mul_le_mul (hkS j hji) (hs j hji) (norm_nonneg _)
          (le_trans (frobRows_nonneg _ _) (hkS j hji)))

/-- The tight chain node bound. Per step `j` the accumulated forcing is
transported by the composed transition `stm P i j` and the velocity columns of
the composed kernels `stm P i j * H_j` (for both the forcing `n_j` and the
gradient defect) and the Frobenius norm of `stm P i j * (H_j' + H_j Â_j)` carry
the growth. The composition is kept exact: the constant factor `stm P i j` is
never separated from the velocity column norm, so the secular growth is that of
the true composed kernel. The step inputs are `c j = m j + ∫_j` and
`slack j = (1 - P j H_j h_j) (b j)`. -/
theorem chain_bound_kernel (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (e0init : E)
    (b m c slack : ℕ → E)
    (Hf Af Âf H'f : ℕ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) (ef nf : ℕ → ℝ → E)
    (hlen kM kS kV kR M F K_R εA εI d : ℕ → ℝ)
    (hbase : b 0 = act (P 0) (e0init + c 0) + slack 0)
    (hsucc : ∀ j, b (j + 1) = act (P (j + 1)) (b j + c (j + 1)) + slack (j + 1))
    (hc : ∀ j, c j = m j + ∫ s in (0 : ℝ)..hlen j, drift (Hf j) (Af j) (H'f j) (ef j) (nf j) s)
    (hslack : ∀ j, slack j = act (1 - P j * Hf j (hlen j)) (b j))
    {i : ℕ}
    (hlen0 : ∀ j, 0 ≤ hlen j)
    (hcont : ∀ j, Continuous (drift (Hf j) (Af j) (H'f j) (ef j) (nf j)))
    (hM0 : ∀ j, 0 ≤ M j) (hK0 : ∀ j, 0 ≤ K_R j)
    (hAp0 : ∀ j s k, (Af j s - Âf j s) 0 k = 0) (hAp1 : ∀ j s k, (Af j s - Âf j s) 1 k = 0)
    (hn0 : ∀ j s, (nf j s) 0 = 0) (hn1 : ∀ j s, (nf j s) 1 = 0)
    (hkM : ∀ j, j ≤ i → frob (stm P i j) ≤ kM j)
    (hkS : ∀ j, j ≤ i → frob (stm P i (j + 1)) ≤ kS j)
    (hkV : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j), frobVel (stm P i j * Hf j s) ≤ kV j)
    (hkR : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j),
      frob (stm P i j * (H'f j s + Hf j s * Âf j s)) ≤ kR j)
    (hεA : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j), frob (Af j s - Âf j s) ≤ εA j)
    (hetube : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j), ‖ef j s‖ ≤ M j)
    (hnb : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j),
      ‖ef j s‖ ≤ M j → ‖nf j s‖ ≤ K_R j * ‖ef j s‖ ^ 2 + F j)
    (hεI : ∀ j, j ≤ i → frob (1 - P j * Hf j (hlen j)) ≤ εI j)
    (hbtube : ∀ j, j ≤ i → ‖b j‖ ≤ M j) (hd : ∀ j, j ≤ i → ‖m j‖ ≤ d j) :
    ‖b i‖ ≤ kM 0 * ‖e0init‖
      + ∑ j ∈ Finset.range (i + 1),
          (kM j * d j
            + hlen j * (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j)
            + kS j * (εI j * M j)) := by
  rw [chain_identity P e0init b c slack hbase hsucc i]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (mulVec_norm_le_frobenius _ _).trans
      (mul_le_mul_of_nonneg_right (hkM 0 (Nat.zero_le _)) (norm_nonneg _))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hji : j ≤ i := by omega
    have hcj : ‖act (stm P i j) (c j)‖
        ≤ kM j * d j
          + (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j) * hlen j := by
      rw [hc j, act_vec_add]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (mulVec_norm_le_frobenius _ _).trans
          (mul_le_mul (hkM j hji) (hd j hji) (norm_nonneg _)
            (le_trans (frob_nonneg _) (hkM j hji)))
      · exact prefixed_int_norm_le (stm P i j) (Hf j) (Af j) (Âf j) (H'f j) (ef j) (nf j)
          (hlen0 j) (hcont j) (hM0 j) (hK0 j) (fun s => hAp0 j s) (fun s => hAp1 j s)
          (fun s => hn0 j s) (fun s => hn1 j s) (hkR j hji) (hkV j hji) (hεA j hji)
          (hetube j hji) (hnb j hji)
    have hsj : ‖act (stm P i (j + 1)) (slack j)‖ ≤ kS j * (εI j * M j) := by
      rw [hslack j]
      have hsl : ‖act (1 - P j * Hf j (hlen j)) (b j)‖ ≤ εI j * M j :=
        (mulVec_norm_le_frobenius _ _).trans
          (mul_le_mul (hεI j hji) (hbtube j hji) (norm_nonneg _)
            (le_trans (frob_nonneg _) (hεI j hji)))
      exact (mulVec_norm_le_frobenius _ _).trans
        (mul_le_mul (hkS j hji) hsl (norm_nonneg _)
          (le_trans (frob_nonneg _) (hkS j hji)))
    calc ‖act (stm P i j) (c j) + act (stm P i (j + 1)) (slack j)‖
        ≤ ‖act (stm P i j) (c j)‖ + ‖act (stm P i (j + 1)) (slack j)‖ := norm_add_le _ _
      _ ≤ (kM j * d j
            + (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j) * hlen j)
            + kS j * (εI j * M j) := add_le_add hcj hsj
      _ = kM j * d j
            + hlen j * (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j)
            + kS j * (εI j * M j) := by ring

/-- The row projected tight chain node bound. Projecting the tight kernel bound
onto a row block `R` (position rows `{0, 1}` or velocity rows `{2, 3}`) replaces
each composed kernel norm by its row restricted version, so position and
velocity errors get separate bounds that still keep the composition exact. -/
theorem chain_bound_kernel_rows (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (e0init : E)
    (b m c slack : ℕ → E) (R : Finset (Fin 4))
    (Hf Af Âf H'f : ℕ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) (ef nf : ℕ → ℝ → E)
    (hlen kM kS kV kR M F K_R εA εI d : ℕ → ℝ)
    (hbase : b 0 = act (P 0) (e0init + c 0) + slack 0)
    (hsucc : ∀ j, b (j + 1) = act (P (j + 1)) (b j + c (j + 1)) + slack (j + 1))
    (hc : ∀ j, c j = m j + ∫ s in (0 : ℝ)..hlen j, drift (Hf j) (Af j) (H'f j) (ef j) (nf j) s)
    (hslack : ∀ j, slack j = act (1 - P j * Hf j (hlen j)) (b j))
    {i : ℕ}
    (hlen0 : ∀ j, 0 ≤ hlen j)
    (hcont : ∀ j, Continuous (drift (Hf j) (Af j) (H'f j) (ef j) (nf j)))
    (hM0 : ∀ j, 0 ≤ M j) (hK0 : ∀ j, 0 ≤ K_R j)
    (hAp0 : ∀ j s k, (Af j s - Âf j s) 0 k = 0) (hAp1 : ∀ j s k, (Af j s - Âf j s) 1 k = 0)
    (hn0 : ∀ j s, (nf j s) 0 = 0) (hn1 : ∀ j s, (nf j s) 1 = 0)
    (hkM : ∀ j, j ≤ i → frobRows R (stm P i j) ≤ kM j)
    (hkS : ∀ j, j ≤ i → frobRows R (stm P i (j + 1)) ≤ kS j)
    (hkV : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j),
      frobRowsVel R (stm P i j * Hf j s) ≤ kV j)
    (hkR : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j),
      frobRows R (stm P i j * (H'f j s + Hf j s * Âf j s)) ≤ kR j)
    (hεA : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j), frob (Af j s - Âf j s) ≤ εA j)
    (hetube : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j), ‖ef j s‖ ≤ M j)
    (hnb : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j),
      ‖ef j s‖ ≤ M j → ‖nf j s‖ ≤ K_R j * ‖ef j s‖ ^ 2 + F j)
    (hεIr : ∀ j, j ≤ i → frob (1 - P j * Hf j (hlen j)) ≤ εI j)
    (hbtube : ∀ j, j ≤ i → ‖b j‖ ≤ M j) (hd : ∀ j, j ≤ i → ‖m j‖ ≤ d j) :
    ‖projRows R (b i)‖ ≤ kM 0 * ‖e0init‖
      + ∑ j ∈ Finset.range (i + 1),
          (kM j * d j
            + hlen j * (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j)
            + kS j * (εI j * M j)) := by
  rw [chain_identity P e0init b c slack hbase hsucc i, projRows_vadd, projRows_vsum]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (projRows_act_le R _ _).trans
      (mul_le_mul_of_nonneg_right (hkM 0 (Nat.zero_le _)) (norm_nonneg _))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hji : j ≤ i := by omega
    have hcj : ‖projRows R (act (stm P i j) (c j))‖
        ≤ kM j * d j
          + (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j) * hlen j := by
      rw [hc j, act_vec_add, projRows_vadd]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (projRows_act_le R _ _).trans
          (mul_le_mul (hkM j hji) (hd j hji) (norm_nonneg _)
            (le_trans (frobRows_nonneg _ _) (hkM j hji)))
      · rw [projRows, ← act_mul]
        exact prefixed_int_norm_le (diagRows R * stm P i j)
          (Hf j) (Af j) (Âf j) (H'f j) (ef j) (nf j) (hlen0 j) (hcont j) (hM0 j) (hK0 j)
          (fun s => hAp0 j s) (fun s => hAp1 j s) (fun s => hn0 j s) (fun s => hn1 j s)
          (fun s hs => by rw [mul_assoc, frob_diagRows_mul]; exact hkR j hji s hs)
          (fun s hs => by rw [mul_assoc, frobVel_diagRows_mul]; exact hkV j hji s hs)
          (hεA j hji) (hetube j hji) (hnb j hji)
    have hsj : ‖projRows R (act (stm P i (j + 1)) (slack j))‖ ≤ kS j * (εI j * M j) := by
      rw [hslack j]
      have hsl : ‖act (1 - P j * Hf j (hlen j)) (b j)‖ ≤ εI j * M j :=
        (mulVec_norm_le_frobenius _ _).trans
          (mul_le_mul (hεIr j hji) (hbtube j hji) (norm_nonneg _)
            (le_trans (frob_nonneg _) (hεIr j hji)))
      exact (projRows_act_le R _ _).trans
        (mul_le_mul (hkS j hji) hsl (norm_nonneg _)
          (le_trans (frobRows_nonneg _ _) (hkS j hji)))
    rw [projRows_vadd]
    calc ‖projRows R (act (stm P i j) (c j)) + projRows R (act (stm P i (j + 1)) (slack j))‖
        ≤ ‖projRows R (act (stm P i j) (c j))‖
            + ‖projRows R (act (stm P i (j + 1)) (slack j))‖ := norm_add_le _ _
      _ ≤ (kM j * d j
            + (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j) * hlen j)
            + kS j * (εI j * M j) := add_le_add hcj hsj
      _ = kM j * d j
            + hlen j * (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j)
            + kS j * (εI j * M j) := by ring

/-! ## Column restricted Frobenius bounds and the split initial term

The initial error `e0` splits into a position block (columns `0, 1`) and a
velocity block (columns `2, 3`), transported by the corresponding column blocks
of the composed transition. The column restricted Frobenius norm bounds each
block separately, so the two initial radii are carried by their own coefficients
rather than by a single combined norm. -/

/-- The Frobenius norm restricted to a set of columns. -/
def frobCols (C : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j ∈ C, (M i j) ^ 2)

/-- The Frobenius norm restricted to a set of rows and a set of columns. -/
def frobRowsCols (R C : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Real.sqrt (∑ i ∈ R, ∑ j ∈ C, (M i j) ^ 2)

theorem frobRowsCols_nonneg (R C : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    0 ≤ frobRowsCols R C M := Real.sqrt_nonneg _

/-- The column block Frobenius bound: if the coordinates of `v` outside `C`
vanish then `‖M v‖` is controlled by the columns of `M` in `C` alone. -/
theorem mulVec_norm_le_frobCols (M : Matrix (Fin 4) (Fin 4) ℝ) (v : E) (C : Finset (Fin 4))
    (hz : ∀ j, j ∉ C → v j = 0) : ‖act M v‖ ≤ frobCols C M * ‖v‖ := by
  rw [EuclideanSpace.norm_eq, frobCols, EuclideanSpace.norm_eq, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hrestrict : ∀ i : Fin 4, (∑ j, M i j * v j) = ∑ j ∈ C, M i j * v j := by
    intro i; symm
    refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
    rw [hz j hj, mul_zero]
  have hvsum : ∑ i, ‖v i‖ ^ 2 = ∑ i, (v i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_; rw [Real.norm_eq_abs, sq_abs]
  calc ∑ i, ‖(act M v) i‖ ^ 2
      = ∑ i, (∑ j ∈ C, M i j * v j) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [act_component, Real.norm_eq_abs, sq_abs, hrestrict]
    _ ≤ ∑ i, (∑ j ∈ C, (M i j) ^ 2) * (∑ j ∈ C, (v j) ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.sum_mul_sq_le_sq_mul_sq _ (fun j => M i j) (fun j => v j)
    _ = (∑ i, ∑ j ∈ C, (M i j) ^ 2) * (∑ j ∈ C, (v j) ^ 2) := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j ∈ C, M i j ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
        rw [hvsum]
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => by positivity)) (by positivity)

theorem frobCols_diagRows_mul (R C : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    frobCols C (diagRows R * M) = frobRowsCols R C M := by
  have hcomp : ∀ i j, (diagRows R * M) i j = if i ∈ R then M i j else 0 := by
    intro i j; rw [diagRows, Matrix.diagonal_mul]; by_cases h : i ∈ R <;> simp [h]
  have hsum : ∑ i, ∑ j ∈ C, ((diagRows R * M) i j) ^ 2 = ∑ i ∈ R, ∑ j ∈ C, (M i j) ^ 2 := by
    calc ∑ i, ∑ j ∈ C, ((diagRows R * M) i j) ^ 2
        = ∑ i, (if i ∈ R then ∑ j ∈ C, (M i j) ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hcomp]; by_cases h : i ∈ R <;> simp [h]
      _ = ∑ i ∈ R, ∑ j ∈ C, (M i j) ^ 2 := by rw [← Finset.sum_filter]; congr 1; ext i; simp
  rw [frobCols, frobRowsCols, hsum]

/-- Row and column block bound: if the coordinates of `v` outside `C` vanish,
the rows in `R` of the action are controlled by the row and column restricted
Frobenius norm. -/
theorem projRows_act_le_cols (R C : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) (v : E)
    (hz : ∀ j, j ∉ C → v j = 0) : ‖projRows R (act M v)‖ ≤ frobRowsCols R C M * ‖v‖ := by
  rw [projRows, ← act_mul]
  calc ‖act (diagRows R * M) v‖ ≤ frobCols C (diagRows R * M) * ‖v‖ :=
        mulVec_norm_le_frobCols _ _ _ hz
    _ = frobRowsCols R C M * ‖v‖ := by rw [frobCols_diagRows_mul]

/-- The split initial transport: the position block (columns `0, 1`) and the
velocity block (columns `2, 3`) of the composed transition carry the position
and velocity parts of the initial error separately. -/
theorem projRows_act_split (R : Finset (Fin 4)) (M : Matrix (Fin 4) (Fin 4) ℝ) (vp vv : E)
    (hp : ∀ j, j ∉ ({0, 1} : Finset (Fin 4)) → vp j = 0)
    (hv : ∀ j, j ∉ ({2, 3} : Finset (Fin 4)) → vv j = 0) :
    ‖projRows R (act M (vp + vv))‖
      ≤ frobRowsCols R ({0, 1} : Finset (Fin 4)) M * ‖vp‖
        + frobRowsCols R ({2, 3} : Finset (Fin 4)) M * ‖vv‖ := by
  rw [act_vec_add, projRows_vadd]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact projRows_act_le_cols R _ M vp hp
  · exact projRows_act_le_cols R _ M vv hv

/-- The row projected tight chain node bound with a split initial term. The
initial error is transported by the column blocks of the composed transition
`stm P i 0`, so its position and velocity radii `e0p` and `e0v` are carried by
their own coefficients `kMp` and `kMv`, tightening the initial contribution.
Otherwise identical to `chain_bound_kernel_rows`. -/
theorem chain_bound_kernel_rows' (P : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (e0init e0init_p e0init_v : E)
    (b m c slack : ℕ → E) (R : Finset (Fin 4))
    (Hf Af Âf H'f : ℕ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) (ef nf : ℕ → ℝ → E)
    (hlen kM kS kV kR M F K_R εA εI d : ℕ → ℝ) (e0p e0v kMp kMv : ℝ)
    (hbase : b 0 = act (P 0) (e0init + c 0) + slack 0)
    (hsucc : ∀ j, b (j + 1) = act (P (j + 1)) (b j + c (j + 1)) + slack (j + 1))
    (hc : ∀ j, c j = m j + ∫ s in (0 : ℝ)..hlen j, drift (Hf j) (Af j) (H'f j) (ef j) (nf j) s)
    (hslack : ∀ j, slack j = act (1 - P j * Hf j (hlen j)) (b j))
    {i : ℕ}
    (he0split : e0init = e0init_p + e0init_v)
    (he0p : ∀ j, j ∉ ({0, 1} : Finset (Fin 4)) → e0init_p j = 0)
    (he0v : ∀ j, j ∉ ({2, 3} : Finset (Fin 4)) → e0init_v j = 0)
    (hkMp0 : frobRowsCols R ({0, 1} : Finset (Fin 4)) (stm P i 0) ≤ kMp)
    (hkMv0 : frobRowsCols R ({2, 3} : Finset (Fin 4)) (stm P i 0) ≤ kMv)
    (he0pb : ‖e0init_p‖ ≤ e0p) (he0vb : ‖e0init_v‖ ≤ e0v)
    (hlen0 : ∀ j, 0 ≤ hlen j)
    (hcont : ∀ j, Continuous (drift (Hf j) (Af j) (H'f j) (ef j) (nf j)))
    (hM0 : ∀ j, 0 ≤ M j) (hK0 : ∀ j, 0 ≤ K_R j)
    (hAp0 : ∀ j s k, (Af j s - Âf j s) 0 k = 0) (hAp1 : ∀ j s k, (Af j s - Âf j s) 1 k = 0)
    (hn0 : ∀ j s, (nf j s) 0 = 0) (hn1 : ∀ j s, (nf j s) 1 = 0)
    (hkM : ∀ j, j ≤ i → frobRows R (stm P i j) ≤ kM j)
    (hkS : ∀ j, j ≤ i → frobRows R (stm P i (j + 1)) ≤ kS j)
    (hkV : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j),
      frobRowsVel R (stm P i j * Hf j s) ≤ kV j)
    (hkR : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j),
      frobRows R (stm P i j * (H'f j s + Hf j s * Âf j s)) ≤ kR j)
    (hεA : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j), frob (Af j s - Âf j s) ≤ εA j)
    (hetube : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j), ‖ef j s‖ ≤ M j)
    (hnb : ∀ j, j ≤ i → ∀ s ∈ Icc (0 : ℝ) (hlen j),
      ‖ef j s‖ ≤ M j → ‖nf j s‖ ≤ K_R j * ‖ef j s‖ ^ 2 + F j)
    (hεIr : ∀ j, j ≤ i → frob (1 - P j * Hf j (hlen j)) ≤ εI j)
    (hbtube : ∀ j, j ≤ i → ‖b j‖ ≤ M j) (hd : ∀ j, j ≤ i → ‖m j‖ ≤ d j) :
    ‖projRows R (b i)‖ ≤ kMp * e0p + kMv * e0v
      + ∑ j ∈ Finset.range (i + 1),
          (kM j * d j
            + hlen j * (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j)
            + kS j * (εI j * M j)) := by
  rw [chain_identity P e0init b c slack hbase hsucc i, projRows_vadd, projRows_vsum]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [he0split]
    refine (projRows_act_split R (stm P i 0) e0init_p e0init_v he0p he0v).trans ?_
    exact add_le_add
      (mul_le_mul hkMp0 he0pb (norm_nonneg _) (le_trans (frobRowsCols_nonneg _ _ _) hkMp0))
      (mul_le_mul hkMv0 he0vb (norm_nonneg _) (le_trans (frobRowsCols_nonneg _ _ _) hkMv0))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hji : j ≤ i := by omega
    have hcj : ‖projRows R (act (stm P i j) (c j))‖
        ≤ kM j * d j
          + (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j) * hlen j := by
      rw [hc j, act_vec_add, projRows_vadd]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (projRows_act_le R _ _).trans
          (mul_le_mul (hkM j hji) (hd j hji) (norm_nonneg _)
            (le_trans (frobRows_nonneg _ _) (hkM j hji)))
      · rw [projRows, ← act_mul]
        exact prefixed_int_norm_le (diagRows R * stm P i j)
          (Hf j) (Af j) (Âf j) (H'f j) (ef j) (nf j) (hlen0 j) (hcont j) (hM0 j) (hK0 j)
          (fun s => hAp0 j s) (fun s => hAp1 j s) (fun s => hn0 j s) (fun s => hn1 j s)
          (fun s hs => by rw [mul_assoc, frob_diagRows_mul]; exact hkR j hji s hs)
          (fun s hs => by rw [mul_assoc, frobVel_diagRows_mul]; exact hkV j hji s hs)
          (hεA j hji) (hetube j hji) (hnb j hji)
    have hsj : ‖projRows R (act (stm P i (j + 1)) (slack j))‖ ≤ kS j * (εI j * M j) := by
      rw [hslack j]
      have hsl : ‖act (1 - P j * Hf j (hlen j)) (b j)‖ ≤ εI j * M j :=
        (mulVec_norm_le_frobenius _ _).trans
          (mul_le_mul (hεIr j hji) (hbtube j hji) (norm_nonneg _)
            (le_trans (frob_nonneg _) (hεIr j hji)))
      exact (projRows_act_le R _ _).trans
        (mul_le_mul (hkS j hji) hsl (norm_nonneg _)
          (le_trans (frobRows_nonneg _ _) (hkS j hji)))
    rw [projRows_vadd]
    calc ‖projRows R (act (stm P i j) (c j)) + projRows R (act (stm P i (j + 1)) (slack j))‖
        ≤ ‖projRows R (act (stm P i j) (c j))‖
            + ‖projRows R (act (stm P i (j + 1)) (slack j))‖ := norm_add_le _ _
      _ ≤ (kM j * d j
            + (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j) * hlen j)
            + kS j * (εI j * M j) := add_le_add hcj hsj
      _ = kM j * d j
            + hlen j * (kV j * (K_R j * M j ^ 2 + F j + εA j * M j) + kR j * M j)
            + kS j * (εI j * M j) := by ring

end GNC.Transported
