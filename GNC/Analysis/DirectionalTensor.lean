import GNC.Lie.Euclidean
import GNC.Analysis.PolynomialObstruction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Directional tensor compression and its error contract.

The Frobenius estimate bounds compression of a homogeneous polynomial term.
A physical-flow certificate also needs the underlying truncation remainder.
The rank-one projection identity reproduces the algebra used by Calkins,
McMahon and Kulik (2025, arXiv:2511.06508, equations 8--24). It does not assert
that an iterative tensor-eigenvector algorithm attains a global optimum.

Restriction of any finite sum of rank-one directional terms to a fixed
linear uncertainty direction remains an ordinary polynomial of the same
degree. Nonlinear input charts and piecewise representations are different
approximation classes.
-/
noncomputable section
namespace GNC.DirectionalTensor
open Finset
variable {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]

def feature (m : ℕ) (x : I → ℝ) (j : Fin m → I) : ℝ := ∏ k, x (j k)
def energy (T : O → J → ℝ) : ℝ := ∑ o, ∑ j, (T o j)^2
def applyFeature (T : O → J → ℝ) (z : J → ℝ) : EuclideanSpace ℝ O :=
  WithLp.toLp 2 (fun o => ∑ j, T o j*z j)
def contract {m : ℕ} (T : O → (Fin m → I) → ℝ) (x : I → ℝ) :=
  applyFeature T (feature m x)
def rankOne {m : ℕ} (u : O → ℝ) (v : I → ℝ) : O → (Fin m → I) → ℝ :=
  fun o j => u o*feature m v j

theorem energy_nonneg (T : O → J → ℝ) : 0 ≤ energy T := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem feature_energy (m : ℕ) (x : I → ℝ) :
    ∑ j, (feature m x j)^2 = (∑ i, (x i)^2)^m := by
  simp only [feature,← Finset.prod_pow]
  exact (Fintype.sum_pow (fun i => (x i)^2) m).symm

theorem feature_pairing (m : ℕ) (v x : I → ℝ) :
    ∑ j, feature m v j*feature m x j = (∑ i, v i*x i)^m := by
  simp only [feature,← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun i => v i*x i) m).symm

theorem applyFeature_bound_sq (T : O → J → ℝ) (z : J → ℝ) :
    ‖applyFeature T z‖^2 ≤ energy T*(∑ j, (z j)^2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ o, (∑ j, (T o j)^2)*(∑ j, (z j)^2) := by
      apply Finset.sum_le_sum
      intro o _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (T o) z
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem contract_bound_sq {m : ℕ} (T : O → (Fin m → I) → ℝ) (x : I → ℝ) :
    ‖contract T x‖^2 ≤ energy T*(∑ i, (x i)^2)^m := by
  simpa only [contract,feature_energy] using applyFeature_bound_sq T (feature m x)

theorem contract_bound {m : ℕ} (T : O → (Fin m → I) → ℝ) (x : I → ℝ) :
    ‖contract T x‖ ≤ Real.sqrt (energy T)*‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖^m := by
  have he := energy_nonneg T
  have h := contract_bound_sq T x
  have hs : (Real.sqrt (energy T))^2 = energy T := Real.sq_sqrt he
  have hn : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖^2 = ∑ i, (x i)^2 :=
    EuclideanSpace.real_norm_sq_eq _
  apply le_of_sq_le_sq _ (by positivity)
  calc
    _ ≤ energy T*(∑ i, (x i)^2)^m := h
    _ = (Real.sqrt (energy T)*‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖^m)^2 := by
      rw [mul_pow,hs,← hn,← pow_mul,← pow_mul]
      rw [Nat.mul_comm m 2]

theorem contract_sub {m : ℕ} (T S : O → (Fin m → I) → ℝ) (x : I → ℝ) :
    contract (T-S) x = contract T x-contract S x := by
  ext o
  simp [contract,applyFeature,sub_mul,Finset.sum_sub_distrib]

omit [Fintype O] in
theorem rankOne_contract {m : ℕ} (u : O → ℝ) (v x : I → ℝ) :
    contract (rankOne (m := m) u v) x =
      (∑ i, v i*x i)^m • (WithLp.toLp 2 u : EuclideanSpace ℝ O) := by
  ext o
  change (∑ j, (u o*feature m v j)*feature m x j) = _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,feature_pairing]
  simp [mul_comm]

/-- Completing the square for a fixed unit feature direction. -/
theorem row_projection_identity (a v : J → ℝ) (y : ℝ) (hv : ∑ j, (v j)^2=1) :
    (∑ j, (a j-y*v j)^2) =
      (∑ j, (a j)^2)-(∑ j, a j*v j)^2+(y-∑ j, a j*v j)^2 := by
  have h : ∀ j, (a j-y*v j)^2 = (a j)^2-2*y*(a j*v j)+y^2*(v j)^2 := by
    intro j; ring
  simp_rw [h]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hv]
  ring

/-- The optimal output for a fixed unit feature is its tensor contraction.
This is a global minimum in the output vector, with a quantified gap. -/
theorem projection_identity (T : O → J → ℝ) (v : J → ℝ) (y : O → ℝ)
    (hv : ∑ j, (v j)^2=1) :
    energy (fun o j => T o j-y o*v j) =
      energy T-‖applyFeature T v‖^2+
        ‖(WithLp.toLp 2 y : EuclideanSpace ℝ O)-applyFeature T v‖^2 := by
  simp only [energy,EuclideanSpace.real_norm_sq_eq,applyFeature]
  simp_rw [row_projection_identity _ v _ hv]
  simp [Finset.sum_add_distrib,Finset.sum_sub_distrib]

theorem rankOne_residual_identity {m : ℕ}
    (T : O → (Fin m → I) → ℝ) (v : I → ℝ) (hv : ∑ i, (v i)^2=1) :
    energy (T-rankOne (fun o => contract T v o) v) = energy T-‖contract T v‖^2 := by
  have hf : ∑ j, (feature m v j)^2=1 := by rw [feature_energy,hv,one_pow]
  have h := projection_identity T (feature m v) (fun o => contract T v o) hf
  simpa [rankOne,contract] using h

/-- Global Frobenius optimality is equivalent to maximizing the norm of
the tensor contraction on unit input directions. An eigensolver must still
establish this maximum; a stationary direction alone is insufficient. -/
theorem rankOne_optimal_iff {m : ℕ} (T : O → (Fin m → I) → ℝ)
    (v : I → ℝ) (hv : ∑ i, (v i)^2=1) :
    (∀ w : I → ℝ, (∑ i, (w i)^2)=1 → ∀ y : O → ℝ,
      energy (T-rankOne (fun o => contract T v o) v) ≤ energy (T-rankOne y w)) ↔
    (∀ w : I → ℝ, (∑ i, (w i)^2)=1 → ‖contract T w‖^2≤‖contract T v‖^2) := by
  constructor
  · intro h w hw
    have hb := h w hw (fun o => contract T w o)
    rw [rankOne_residual_identity T v hv,rankOne_residual_identity T w hw] at hb
    linarith
  · intro h w hw y
    rw [rankOne_residual_identity T v hv]
    have hf : ∑ j, (feature m w j)^2=1 := by rw [feature_energy,hw,one_pow]
    have hfuns : (T-rankOne (m := m) y w) = (fun o j => T o j-y o*feature m w j) := rfl
    rw [hfuns,projection_identity T (feature m w) y hf]
    have hb := h w hw
    change ‖applyFeature T (feature m w)‖^2≤‖contract T v‖^2 at hb
    linarith [sq_nonneg ‖(WithLp.toLp 2 y : EuclideanSpace ℝ O)-applyFeature T (feature m w)‖]

/-- An independent physical remainder must accompany tensor compression. -/
theorem physical_error_bound {m : ℕ} (T S : O → (Fin m → I) → ℝ)
    (x : I → ℝ) (actual base : EuclideanSpace ℝ O) {remainder : ℝ}
    (h : ‖actual-(base+contract T x)‖ ≤ remainder) :
    ‖actual-(base+contract S x)‖ ≤ remainder+
      Real.sqrt (energy (T-S))*‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖^m := by
  have hc := contract_bound (T-S) x
  rw [contract_sub] at hc
  have ht := dist_triangle actual (base+contract T x) (base+contract S x)
  simp only [dist_eq_norm,add_sub_add_left_eq_sub] at ht
  exact ht.trans (add_le_add h hc)

/-- A complete finite-order bound, including every tensor-compression
error and an independently supplied physical-flow remainder. The weights
may include the Taylor factorials and need not be positive. -/
theorem physical_series_bound {n : ℕ} (order : Fin n → ℕ)
    (T S : (k : Fin n) → O → (Fin (order k) → I) → ℝ)
    (weight : Fin n → ℝ) (x : I → ℝ) (actual base : EuclideanSpace ℝ O)
    {remainder : ℝ} (h : ‖actual-(base+∑ k, weight k • contract (T k) x)‖ ≤ remainder) :
    ‖actual-(base+∑ k, weight k • contract (S k) x)‖ ≤ remainder+
      ∑ k, |weight k| * Real.sqrt (energy (T k-S k))*
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖^(order k) := by
  have hs : ‖(∑ k, weight k • contract (T k) x)-(∑ k, weight k • contract (S k) x)‖ ≤
      ∑ k, |weight k| * Real.sqrt (energy (T k-S k))*
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖^(order k) := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro k _
    rw [← smul_sub,← contract_sub,norm_smul,Real.norm_eq_abs,mul_assoc]
    exact mul_le_mul_of_nonneg_left (contract_bound (T k-S k) x) (abs_nonneg _)
  have ht := dist_triangle actual (base+∑ k, weight k • contract (T k) x)
    (base+∑ k, weight k • contract (S k) x)
  simp only [dist_eq_norm,add_sub_add_left_eq_sub] at ht
  exact ht.trans (add_le_add h hs)

omit [Fintype O] in
/-- A tensor with one scalar input is already exactly rank one, at every
order. There is no approximation from input-direction compression to remove. -/
theorem scalar_rankOne_exact {m : ℕ} (T : O → (Fin m → Unit) → ℝ) :
    rankOne (fun o => contract T (fun _ => 1) o) (fun _ : Unit => (1:ℝ)) = T := by
  ext o j
  simp [rankOne,contract,applyFeature,feature]

def ridgeSeries {n : ℕ} (degree : Fin n → ℕ) (a : Fin n → EuclideanSpace ℝ O)
    (v : Fin n → I → ℝ) (x : I → ℝ) : EuclideanSpace ℝ O :=
  ∑ k, (∑ i, v k i*x i)^(degree k) • a k

def linePolynomial {n : ℕ} (degree : Fin n → ℕ) (a : Fin n → EuclideanSpace ℝ O)
    (v : Fin n → I → ℝ) (direction : I → ℝ) (o : O) : Polynomial ℝ :=
  ∑ k, Polynomial.C (a k o*(∑ i, v k i*direction i)^(degree k))*Polynomial.X^(degree k)

omit [Fintype O] in
theorem linePolynomial_degree {n d : ℕ} (degree : Fin n → ℕ)
    (a : Fin n → EuclideanSpace ℝ O) (v : Fin n → I → ℝ) (direction : I → ℝ)
    (hd : ∀ k, degree k≤d) (o : O) :
    (linePolynomial degree a v direction o).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (hd k)

theorem linePolynomial_eval {n : ℕ} (degree : Fin n → ℕ)
    (a : Fin n → EuclideanSpace ℝ O) (v : Fin n → I → ℝ) (direction : I → ℝ)
    (θ : ℝ) :
    WithLp.toLp 2 (fun o => (linePolynomial degree a v direction o).eval θ) =
      ridgeSeries degree a v (fun i => θ*direction i) := by
  ext o
  simp only [linePolynomial,Polynomial.eval_finset_sum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,ridgeSeries,
    WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  have h : (∑ i, v k i*(θ*direction i)) = θ*(∑ i, v k i*direction i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [h,mul_pow]
  ring

end GNC.DirectionalTensor
