import GNC.Dynamics.PlanarCoastDefect
import GNC.Dynamics.GravityRemainderBall
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Curvature (transition-matrix) certificate data for the planar two-body
coast. This module adds, on top of the scalar defect certificate of
`PlanarCoastDefect`, the true gravity gradient as a real matrix, its Taylor
remainder on a displacement tube, the polynomial gradient candidate and its
rational error, and the linearized error dynamics of a true coast solution
about a polynomial candidate.

Matrices act on `EuclideanSpace ℝ (Fin n)` through `Matrix.toEuclideanCLM`,
and the matrix size is measured by the Frobenius norm `frob M = sqrt (Σ Mᵢⱼ²)`,
which satisfies the operator bound `‖M v‖ ≤ frob M * ‖v‖`. All rational
certificate quantities are bounded above by coefficient sums so that a
finite rational check certifies a real inequality on the whole step.
-/
noncomputable section
open Set Finset Matrix
namespace GNC.PlanarCoast
open Planning.PolynomialKernel PolynomialBounds
open scoped RealInnerProductSpace

/-! ### Matrix action and the Frobenius operator bound -/

/-- A real square matrix acting on Euclidean space through `toEuclideanCLM`. -/
noncomputable def act {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := toEuclideanCLM (𝕜 := ℝ) M v

theorem act_component {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) : (act M v) i = ∑ j, M i j * v j := by
  have h : (act M v) = (M *ᵥ (v : Fin n → ℝ)) := ofLp_toEuclideanCLM M v
  rw [h]; rfl

theorem act_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    act (M + N) v = act M v + act N v := by
  simp only [act, map_add, ContinuousLinearMap.add_apply]

theorem act_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    act (M - N) v = act M v - act N v := by
  simp only [act, map_sub, ContinuousLinearMap.sub_apply]

/-- Frobenius norm: the root of the sum of squared entries. -/
noncomputable def frob {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (M i j) ^ 2)

theorem frob_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frob M := Real.sqrt_nonneg _

/-- The Frobenius operator bound `‖M v‖ ≤ frob M * ‖v‖`, from Cauchy-Schwarz. -/
theorem mulVec_norm_le_frobenius {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : ‖act M v‖ ≤ frob M * ‖v‖ := by
  have hnn : 0 ≤ frob M * ‖v‖ := mul_nonneg (frob_nonneg M) (norm_nonneg _)
  have hsq : ‖act M v‖ ^ 2 ≤ (frob M * ‖v‖) ^ 2 := by
    have hv : ‖v‖ ^ 2 = ∑ j, (v j) ^ 2 := EuclideanSpace.real_norm_sq_eq v
    have ha : ‖act M v‖ ^ 2 = ∑ i, (∑ j, M i j * v j) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]; simp only [act_component]
    rw [ha, mul_pow, frob, Real.sq_sqrt (by positivity), hv, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).mp hsq

/-- A Frobenius bound from a rational square witness: `Σ Mᵢⱼ² ≤ B²` gives
`frob M ≤ B`, keeping the decidable check free of square roots. -/
theorem frob_le_of_sq {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) {B : ℝ}
    (hsum : ∑ i, ∑ j, (N i j) ^ 2 ≤ B ^ 2) (hB : 0 ≤ B) : frob N ≤ B := by
  rw [frob, Real.sqrt_le_iff]; exact ⟨hB, hsum⟩

/-- Entry bounds give a Frobenius bound. -/
theorem frob_le_of_entries {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → Fin n → ℝ)
    {B : ℝ} (hb : ∀ i j, |N i j| ≤ b i j) (hsum : ∑ i, ∑ j, (b i j) ^ 2 ≤ B ^ 2)
    (hB : 0 ≤ B) : frob N ≤ B := by
  refine frob_le_of_sq N (le_trans ?_ hsum) hB
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h := hb i j
  nlinarith [abs_nonneg (N i j), sq_abs (N i j)]

/-! ### The true gravity gradient as a `2×2` matrix -/

/-- The plane inner product in coordinates. -/
theorem euclid_inner_two (q v : E2) : (inner ℝ q v : ℝ) = q 0 * v 0 + q 1 * v 1 := by
  change (∑ i, v i * q i) = _
  rw [Fin.sum_univ_two]; ring

/-- The true gradient `Dg(q) = -‖q‖⁻³ I + 3‖q‖⁻⁵ q qᵀ` of the field
`g(q) = -q/‖q‖³` on the plane, written as a `2×2` real matrix. -/
noncomputable def Dg (q : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => 3 * q i * q j / ‖q‖^5 - (if i = j then 1 / ‖q‖^3 else 0)

/-- The matrix `Dg q` acts as the analytic gravity gradient. -/
theorem Dg_act (q v : E2) : act (Dg q) v = Gravity.gradient 1 q v := by
  ext i
  fin_cases i <;>
    simp only [act_component, Fin.sum_univ_two, Dg, Gravity.gradient,
      WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      euclid_inner_two q v, Fin.mk_zero, Fin.mk_one, Fin.isValue, Fin.reduceEq,
      if_true, if_false] <;>
    ring

/-! ### Taylor remainder of the field on a displacement ball -/

/-- Second-order remainder of the field on the tube of radius `M` around a
point of radius at least `ρmin > M`, with the explicit constant
`K_R = 3 / (ρmin - M)⁴`. -/
theorem field_taylor_remainder (q p : E2) {ρmin M : ℝ} (hM : M < ρmin) (hq : ρmin ≤ ‖q‖)
    (hp : ‖p‖ ≤ M) :
    ‖Gravity.field 1 (q + p) - Gravity.field 1 q - act (Dg q) p‖ ≤ (3 / (ρmin - M)^4) * ‖p‖^2 := by
  rw [Dg_act]
  simpa using Gravity.remainder_quadratic 1 (by norm_num) q p hM hq hp

/-! ### Stacking plane vectors into the state space `EuclideanSpace ℝ (Fin 4)` -/

/-- Four real coordinates as a Euclidean 4-vector. -/
def pack4 (a b c d : ℝ) : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 ![a, b, c, d]

/-- Stack a position and a velocity plane vector into a state 4-vector. -/
def join2 (x y : E2) : EuclideanSpace ℝ (Fin 4) := pack4 (x 0) (x 1) (y 0) (y 1)

theorem pack4_add (a b c d a' b' c' d' : ℝ) :
    pack4 a b c d + pack4 a' b' c' d' = pack4 (a+a') (b+b') (c+c') (d+d') := by
  ext i; fin_cases i <;> rfl

theorem join2_add (x y x' y' : E2) : join2 x y + join2 x' y' = join2 (x+x') (y+y') := by
  rw [join2, join2, join2, pack4_add]; rfl

theorem pack4_norm_sq (a b c d : ℝ) : ‖pack4 a b c d‖^2 = a^2+b^2+c^2+d^2 := by
  simp [pack4, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]

theorem join2_norm_sq (x y : E2) : ‖join2 x y‖^2 = ‖x‖^2 + ‖y‖^2 := by
  rw [join2, pack4_norm_sq, EuclideanSpace.real_norm_sq_eq x, EuclideanSpace.real_norm_sq_eq y,
    Fin.sum_univ_two, Fin.sum_univ_two]; ring

theorem join2_left_zero_norm (y : E2) : ‖join2 0 y‖ = ‖y‖ := by
  have h : ‖join2 0 y‖^2 = ‖y‖^2 := by rw [join2_norm_sq]; simp
  have hc := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hc

theorem e2_proj_hasDerivAt {A : ℝ → E2} {A' : E2} {t : ℝ}
    (h : HasDerivAt A A' t) (i : Fin 2) : HasDerivAt (fun s => A s i) (A' i) t := by
  let L : E2 →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toContinuousLinearMap
  have hL : ∀ a : E2, L a = a i := fun _ => rfl
  simpa only [Function.comp_def, hL] using L.hasFDerivAt.comp_hasDerivAt t h

theorem pack4_hasDerivAt {f g p q : ℝ → ℝ} {f' g' p' q' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t)
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => pack4 (f s) (g s) (p s) (q s)) (pack4 f' g' p' q') t := by
  have hpi : HasDerivAt (fun s => ![f s, g s, p s, q s]) ![f', g', p', q'] t := by
    apply hasDerivAt_pi.mpr; intro i; fin_cases i <;> simpa
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt t hpi

theorem join2_hasDerivAt {X Y : ℝ → E2} {X' Y' : E2} {t : ℝ}
    (hX : HasDerivAt X X' t) (hY : HasDerivAt Y Y' t) :
    HasDerivAt (fun s => join2 (X s) (Y s)) (join2 X' Y') t :=
  pack4_hasDerivAt (e2_proj_hasDerivAt hX 0) (e2_proj_hasDerivAt hX 1)
    (e2_proj_hasDerivAt hY 0) (e2_proj_hasDerivAt hY 1)

/-! ### The state matrix `A(t) = [[0, I], [Dg, 0]]` and its block action -/

/-- The linearized state matrix of the coast about a point of the plane. -/
noncomputable def Amat (q : E2) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    ![![0, 0, 1, 0], ![0, 0, 0, 1], ![Dg q 0 0, Dg q 0 1, 0, 0], ![Dg q 1 0, Dg q 1 1, 0, 0]] i j

/-- Block action: the state matrix maps `(x, y)` to `(y, Dg q · x)`. -/
theorem act_Amat (q x y : E2) : act (Amat q) (join2 x y) = join2 y (act (Dg q) x) := by
  have dz0 : (act (Dg q) x) 0 = Dg q 0 0 * x 0 + Dg q 0 1 * x 1 := by
    rw [act_component, Fin.sum_univ_two]
  have dz1 : (act (Dg q) x) 1 = Dg q 1 0 * x 0 + Dg q 1 1 * x 1 := by
    rw [act_component, Fin.sum_univ_two]
  have jx0 : (join2 x y) 0 = x 0 := rfl
  have jx1 : (join2 x y) 1 = x 1 := rfl
  have jy0 : (join2 x y) 2 = y 0 := rfl
  have jy1 : (join2 x y) 3 = y 1 := rfl
  ext i
  rw [act_component, Fin.sum_univ_four, jx0, jx1, jy0, jy1]
  fin_cases i
  · show Amat q 0 0 * x 0 + Amat q 0 1 * x 1 + Amat q 0 2 * y 0 + Amat q 0 3 * y 1 = y 0
    simp only [Amat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]; ring
  · show Amat q 1 0 * x 0 + Amat q 1 1 * x 1 + Amat q 1 2 * y 0 + Amat q 1 3 * y 1 = y 1
    simp only [Amat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]; ring
  · show Amat q 2 0 * x 0 + Amat q 2 1 * x 1 + Amat q 2 2 * y 0 + Amat q 2 3 * y 1
        = (act (Dg q) x) 0
    rw [dz0]; simp only [Amat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]; ring
  · show Amat q 3 0 * x 0 + Amat q 3 1 * x 1 + Amat q 3 2 * y 0 + Amat q 3 3 * y 1
        = (act (Dg q) x) 1
    rw [dz1]; simp only [Amat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]; ring

/-! ### The error dynamics of a true coast solution about the candidate -/

open Candidate

/-- The linearized error dynamics. Writing `e = (truePos - pos, trueVel - dpos)`,
the error satisfies `e' = A(t) e + n(t)` with the noise `n` supported on the
velocity components and bounded by `K_R ‖p‖² + defect` inside the tube
`‖p‖ ≤ M`. -/
theorem error_dynamics (c : Candidate) (hv : c.Valid) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h)
    {M : ℝ} (hM : M < c.rhoMin) {w : ℝ → Fin 4 → ℝ}
    (hw : HasDerivAt w (PolynomialOrbit.physicalRate 0 (w t)) t)
    (hp : ‖truePos w t - c.pos t‖ ≤ M) :
    HasDerivAt (fun s => join2 (truePos w s - c.pos s) (trueVel w s - c.dpos s))
        (act (Amat (c.pos t)) (join2 (truePos w t - c.pos t) (trueVel w t - c.dpos t))
          + join2 0 (Gravity.field 1 (truePos w t) - c.acc t
              - act (Dg (c.pos t)) (truePos w t - c.pos t))) t
      ∧ (join2 (0 : E2) (Gravity.field 1 (truePos w t) - c.acc t
              - act (Dg (c.pos t)) (truePos w t - c.pos t))) 0 = 0
      ∧ (join2 (0 : E2) (Gravity.field 1 (truePos w t) - c.acc t
              - act (Dg (c.pos t)) (truePos w t - c.pos t))) 1 = 0
      ∧ ‖join2 (0 : E2) (Gravity.field 1 (truePos w t) - c.acc t
              - act (Dg (c.pos t)) (truePos w t - c.pos t))‖
          ≤ (3 / ((c.rhoMin : ℝ) - M)^4) * ‖truePos w t - c.pos t‖^2 + c.defect := by
  set p := truePos w t - c.pos t with hpdef
  refine ⟨?_, rfl, rfl, ?_⟩
  · have hd := join2_hasDerivAt (c.errorPos_hasDerivAt hw) (c.errorVel_hasDerivAt hw)
    have heq : act (Amat (c.pos t)) (join2 (truePos w t - c.pos t) (trueVel w t - c.dpos t))
          + join2 0 (Gravity.field 1 (truePos w t) - c.acc t - act (Dg (c.pos t)) p)
        = join2 (trueVel w t - c.dpos t) (Gravity.field 1 (truePos w t) - c.acc t) := by
      rw [act_Amat, join2_add]; congr 1 <;> abel
    rw [heq]; exact hd
  · rw [join2_left_zero_norm]
    have hqrad : (c.rhoMin : ℝ) ≤ ‖c.pos t‖ := c.rhoMin_le_norm_pos hv ht
    have htp : truePos w t = c.pos t + p := by rw [hpdef]; abel
    have hrem := field_taylor_remainder (c.pos t) p hM hqrad hp
    rw [← htp] at hrem
    have hdef : ‖Gravity.field 1 (c.pos t) - c.acc t‖ ≤ (c.defect : ℝ) := by
      rw [norm_sub_rev]; exact c.defect_bound hv ht
    have hsplit : Gravity.field 1 (truePos w t) - c.acc t - act (Dg (c.pos t)) p
        = (Gravity.field 1 (truePos w t) - Gravity.field 1 (c.pos t) - act (Dg (c.pos t)) p)
          + (Gravity.field 1 (c.pos t) - c.acc t) := by abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hrem hdef)

/-! ### The polynomial gradient candidate and the rational gradient error -/

/-- Inverse-radius identity for the cube, factoring `1-z³` and `1-z²`. -/
theorem abs_ratio_cube {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) :
    |u^3 - 1/r^3| = |r^2*u^2 - 1| * (1 + r*u + (r*u)^2) / ((1 + r*u) * r^3) := by
  set z := r*u with hz
  have h1z : (0:ℝ) < 1 + z := by have : 0 ≤ z := mul_nonneg hr.le hu; linarith
  have hr3 : (0:ℝ) < r^3 := by positivity
  have e1 : u^3 - 1/r^3 = (z^3 - 1)/r^3 := by rw [hz]; field_simp
  have e2 : r^2*u^2 - 1 = z^2 - 1 := by rw [hz]; ring
  rw [e1, e2, abs_div, abs_of_pos hr3,
     show z^3 - 1 = (z-1)*(1+z+z^2) by ring, show z^2-1 = (z-1)*(1+z) by ring,
     abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1+z+z^2), abs_of_nonneg h1z.le]
  field_simp

/-- Inverse-radius identity for the fifth power, factoring `1-z⁵` and `1-z²`. -/
theorem abs_ratio_quint {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) :
    |u^5 - 1/r^5| = |r^2*u^2 - 1| * (1 + r*u + (r*u)^2 + (r*u)^3 + (r*u)^4)
      / ((1 + r*u) * r^5) := by
  set z := r*u with hz
  have h1z : (0:ℝ) < 1 + z := by have : 0 ≤ z := mul_nonneg hr.le hu; linarith
  have hr5 : (0:ℝ) < r^5 := by positivity
  have e1 : u^5 - 1/r^5 = (z^5 - 1)/r^5 := by rw [hz]; field_simp
  have e2 : r^2*u^2 - 1 = z^2 - 1 := by rw [hz]; ring
  rw [e1, e2, abs_div, abs_of_pos hr5,
     show z^5 - 1 = (z-1)*(1+z+z^2+z^3+z^4) by ring, show z^2-1 = (z-1)*(1+z) by ring,
     abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1+z+z^2+z^3+z^4),
     abs_of_nonneg h1z.le]
  field_simp

/-- Rational bound of `|û³ - 1/ρ³|` on the step. -/
def A3 (c : Candidate) : ℚ := c.chi * (1 + c.zMax + c.zMax^2) / ((1 + c.zMin) * c.rhoMin^3)
/-- Rational bound of `|û⁵ - 1/ρ⁵|` on the step. -/
def A5 (c : Candidate) : ℚ :=
  c.chi * (1 + c.zMax + c.zMax^2 + c.zMax^3 + c.zMax^4) / ((1 + c.zMin) * c.rhoMin^5)

theorem absDiff_cube_le (c : Candidate) (hv : c.Valid) (hρ : 0 < c.rhoMin)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    |c.invRadius t ^ 3 - 1/‖c.pos t‖^3| ≤ (A3 c : ℝ) := by
  set R := ‖c.pos t‖ with hR
  set U := c.invRadius t with hU
  have hrp : 0 < R := c.norm_pos_pos hv ht
  have huMin : (0:ℝ) < c.uMin := by exact_mod_cast hv.2.2.1
  have hu0 : 0 ≤ U := huMin.le.trans (c.uMin_le_invRadius ht)
  have hrmin : (c.rhoMin:ℝ) ≤ R := c.rhoMin_le_norm_pos hv ht
  have hρr : (0:ℝ) < (c.rhoMin:ℝ) := by exact_mod_cast hρ
  have hzmax : R*U ≤ (c.zMax:ℝ) := by
    rw [zMax]; push_cast
    exact mul_le_mul (c.norm_pos_le_rhoMax hv ht) (c.invRadius_le_uMax ht) hu0
      (by exact_mod_cast hv.2.2.2.2.1)
  have hzmin : (c.zMin:ℝ) ≤ R*U := by
    rw [zMin]; push_cast
    exact mul_le_mul hrmin (c.uMin_le_invRadius ht) huMin.le hrp.le
  have hzmin0 : (0:ℝ) ≤ (c.zMin:ℝ) := by
    rw [zMin]; push_cast; exact mul_nonneg (by exact_mod_cast hv.2.2.2.1) huMin.le
  have hchi0 : (0:ℝ) ≤ (c.chi:ℝ) := by unfold chi; exact_mod_cast bound_nonneg c.chiPoly hv.1
  have hzmax0 : (0:ℝ) ≤ (c.zMax:ℝ) := hzmin0.trans (hzmin.trans hzmax)
  have hchi : |R^2*U^2 - 1| ≤ (c.chi:ℝ) := by
    rw [hR, hU, ← chiPoly_eval]; exact ev_abs_le _ (step_abs ht)
  rw [abs_ratio_cube hrp hu0]
  have hnum_le : |R^2*U^2 - 1| * (1 + R*U + (R*U)^2)
      ≤ (c.chi:ℝ) * (1 + (c.zMax:ℝ) + (c.zMax:ℝ)^2) := by
    apply mul_le_mul hchi _ (by positivity) hchi0
    nlinarith [hzmax, mul_nonneg hrp.le hu0]
  have hden_le : (1 + (c.zMin:ℝ)) * (c.rhoMin:ℝ)^3 ≤ (1 + R*U) * R^3 := by
    apply mul_le_mul (by linarith) _ (by positivity) (by linarith)
    exact pow_le_pow_left₀ hρr.le hrmin 3
  have hA3 : (A3 c : ℝ)
      = (c.chi:ℝ) * (1 + (c.zMax:ℝ) + (c.zMax:ℝ)^2) / ((1 + (c.zMin:ℝ)) * (c.rhoMin:ℝ)^3) := by
    unfold A3; push_cast; ring
  rw [hA3]
  exact div_le_div₀ (mul_nonneg hchi0 (by nlinarith [hzmax0, sq_nonneg (c.zMax:ℝ)])) hnum_le (mul_pos (by linarith) (pow_pos hρr 3)) hden_le

theorem absDiff_quint_le (c : Candidate) (hv : c.Valid) (hρ : 0 < c.rhoMin)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    |c.invRadius t ^ 5 - 1/‖c.pos t‖^5| ≤ (A5 c : ℝ) := by
  set R := ‖c.pos t‖ with hR
  set U := c.invRadius t with hU
  have hrp : 0 < R := c.norm_pos_pos hv ht
  have huMin : (0:ℝ) < c.uMin := by exact_mod_cast hv.2.2.1
  have hu0 : 0 ≤ U := huMin.le.trans (c.uMin_le_invRadius ht)
  have hrmin : (c.rhoMin:ℝ) ≤ R := c.rhoMin_le_norm_pos hv ht
  have hρr : (0:ℝ) < (c.rhoMin:ℝ) := by exact_mod_cast hρ
  have hzmax : R*U ≤ (c.zMax:ℝ) := by
    rw [zMax]; push_cast
    exact mul_le_mul (c.norm_pos_le_rhoMax hv ht) (c.invRadius_le_uMax ht) hu0
      (by exact_mod_cast hv.2.2.2.2.1)
  have hzmin : (c.zMin:ℝ) ≤ R*U := by
    rw [zMin]; push_cast
    exact mul_le_mul hrmin (c.uMin_le_invRadius ht) huMin.le hrp.le
  have hzmin0 : (0:ℝ) ≤ (c.zMin:ℝ) := by
    rw [zMin]; push_cast; exact mul_nonneg (by exact_mod_cast hv.2.2.2.1) huMin.le
  have hz0 : 0 ≤ R*U := mul_nonneg hrp.le hu0
  have hchi0 : (0:ℝ) ≤ (c.chi:ℝ) := by unfold chi; exact_mod_cast bound_nonneg c.chiPoly hv.1
  have hzmax0 : (0:ℝ) ≤ (c.zMax:ℝ) := hzmin0.trans (hzmin.trans hzmax)
  have hchi : |R^2*U^2 - 1| ≤ (c.chi:ℝ) := by
    rw [hR, hU, ← chiPoly_eval]; exact ev_abs_le _ (step_abs ht)
  rw [abs_ratio_quint hrp hu0]
  have hnum_le : |R^2*U^2 - 1| * (1 + R*U + (R*U)^2 + (R*U)^3 + (R*U)^4)
      ≤ (c.chi:ℝ) * (1 + (c.zMax:ℝ) + (c.zMax:ℝ)^2 + (c.zMax:ℝ)^3 + (c.zMax:ℝ)^4) := by
    apply mul_le_mul hchi _ (by positivity) hchi0
    have hle : R*U ≤ (c.zMax:ℝ) := hzmax
    have h0 : 0 ≤ R*U := hz0
    nlinarith [hle, h0, pow_le_pow_left₀ h0 hle 2, pow_le_pow_left₀ h0 hle 3,
      pow_le_pow_left₀ h0 hle 4]
  have hden_le : (1 + (c.zMin:ℝ)) * (c.rhoMin:ℝ)^5 ≤ (1 + R*U) * R^5 := by
    apply mul_le_mul (by linarith) _ (by positivity) (by linarith)
    exact pow_le_pow_left₀ hρr.le hrmin 5
  have hA5 : (A5 c : ℝ)
      = (c.chi:ℝ) * (1 + (c.zMax:ℝ) + (c.zMax:ℝ)^2 + (c.zMax:ℝ)^3 + (c.zMax:ℝ)^4)
        / ((1 + (c.zMin:ℝ)) * (c.rhoMin:ℝ)^5) := by
    unfold A5; push_cast; ring
  rw [hA5]
  exact div_le_div₀ (mul_nonneg hchi0 (by nlinarith [hzmax0, pow_nonneg hzmax0 2, pow_nonneg hzmax0 3, pow_nonneg hzmax0 4])) hnum_le (mul_pos (by linarith) (pow_pos hρr 5)) hden_le

/-- Lower-left block of the polynomial gradient candidate,
`Â_lower = -û³ I + 3 û⁵ q̂ q̂ᵀ`, in real coordinates. -/
noncomputable def Alower (c : Candidate) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => 3 * (c.invRadius t)^5 * (c.pos t) i * (c.pos t) j
    - (if i = j then (c.invRadius t)^3 else 0)

/-- Rational bound of the gradient candidate error `‖Dg(q̂) - Â_lower‖`. -/
def epsA (c : Candidate) : ℚ := 3 * c.rho2Max * A5 c + 2 * A3 c

/-- The polynomial gradient candidate approximates the true gradient with a
Frobenius error at most `epsA c`. -/
theorem gradient_candidate_error (c : Candidate) (hv : c.Valid) (hρ : 0 < c.rhoMin)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    frob (Dg (c.pos t) - Alower c t) ≤ (epsA c : ℝ) := by
  set R := ‖c.pos t‖ with hR
  set U := c.invRadius t with hU
  have hrp : 0 < R := c.norm_pos_pos hv ht
  have hkey : ∑ i, ∑ j, ((Dg (c.pos t) - Alower c t) i j)^2
      = 9*(1/R^5 - U^5)^2*(((c.pos t) 0)^2 + ((c.pos t) 1)^2)^2
        - 6*(1/R^5 - U^5)*(1/R^3 - U^3)*(((c.pos t) 0)^2 + ((c.pos t) 1)^2)
        + 2*(1/R^3 - U^3)^2 := by
    simp only [Fin.sum_univ_two, Matrix.sub_apply, Dg, Alower, ← hR, ← hU, Fin.isValue,
      Fin.reduceEq, ↓reduceIte]
    ring
  set a := 1/R^5 - U^5 with hae
  set b := 1/R^3 - U^3 with hbe
  set S := ((c.pos t) 0)^2 + ((c.pos t) 1)^2 with hSe
  have hSnn : 0 ≤ S := by rw [hSe]; positivity
  have hSval : S = R^2 := by
    rw [hSe, hR, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hSmax : S ≤ (c.rho2Max : ℝ) := by rw [hSval, hR]; exact c.norm_pos_sq_le ht
  have haA5 : |a| ≤ (A5 c : ℝ) := by
    rw [hae, hR, hU, abs_sub_comm]; exact absDiff_quint_le c hv hρ ht
  have hbA3 : |b| ≤ (A3 c : ℝ) := by
    rw [hbe, hR, hU, abs_sub_comm]; exact absDiff_cube_le c hv hρ ht
  have hA5nn : (0:ℝ) ≤ (A5 c : ℝ) := (abs_nonneg a).trans haA5
  have hA3nn : (0:ℝ) ≤ (A3 c : ℝ) := (abs_nonneg b).trans hbA3
  have hepsA : (epsA c : ℝ) = 3 * (c.rho2Max:ℝ) * (A5 c:ℝ) + 2 * (A3 c:ℝ) := by
    unfold epsA; push_cast; ring
  have hB : 3 * |a| * S + 2 * |b| ≤ (epsA c : ℝ) := by
    rw [hepsA]
    nlinarith [mul_le_mul haA5 hSmax hSnn hA5nn, hbA3, hA3nn]
  have hBnn : 0 ≤ 3 * |a| * S + 2 * |b| := by positivity
  refine frob_le_of_sq _ ?_ (hBnn.trans hB)
  rw [hkey]
  have hstep : 9*a^2*S^2 - 6*a*b*S + 2*b^2 ≤ (3 * |a| * S + 2 * |b|)^2 := by
    nlinarith [sq_nonneg b, mul_nonneg (abs_nonneg a) (abs_nonneg b), neg_abs_le (a*b),
      abs_mul a b, hSnn, sq_abs a, sq_abs b,
      mul_nonneg (mul_nonneg (abs_nonneg a) (abs_nonneg b)) hSnn]
  exact hstep.trans (pow_le_pow_left₀ hBnn hB 2)


/-! ### Polynomial matrices for the transition candidate -/

/-- A `4×4` matrix of rational time polynomials. -/
abbrev PolyMat := Matrix (Fin 4) (Fin 4) (List ℚ)

/-- Real evaluation of a polynomial matrix at a time. -/
noncomputable def realMat (P : PolyMat) (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => ev (P i j) t

/-- Entrywise polynomial sum. -/
def pAdd (P Q : PolyMat) : PolyMat := fun i j => add (P i j) (Q i j)
/-- Entrywise polynomial difference. -/
def pSub (P Q : PolyMat) : PolyMat := fun i j => subtract (P i j) (Q i j)
/-- Polynomial matrix product (`4×4`). -/
def pMul (P Q : PolyMat) : PolyMat := fun i j =>
  add (multiply (P i 0) (Q 0 j)) (add (multiply (P i 1) (Q 1 j))
    (add (multiply (P i 2) (Q 2 j)) (multiply (P i 3) (Q 3 j))))
/-- Polynomial identity matrix. -/
def pId : PolyMat := fun i j => if i = j then [1] else []
/-- Entrywise polynomial derivative. -/
def pDeriv (P : PolyMat) : PolyMat := fun i j => differentiate (P i j)

theorem realMat_add (P Q : PolyMat) (t : ℝ) :
    realMat (pAdd P Q) t = realMat P t + realMat Q t := by
  ext i j; simp only [realMat, pAdd, Matrix.add_apply, ev_add]
theorem realMat_sub (P Q : PolyMat) (t : ℝ) :
    realMat (pSub P Q) t = realMat P t - realMat Q t := by
  ext i j; simp only [realMat, pSub, Matrix.sub_apply, ev_subtract]
theorem realMat_id (t : ℝ) : realMat pId t = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; simp only [realMat, pId, Matrix.one_apply]
  by_cases h : i = j <;> simp [h, ev_cons, ev_nil]
theorem realMat_mul (P Q : PolyMat) (t : ℝ) :
    realMat (pMul P Q) t = realMat P t * realMat Q t := by
  ext i j
  simp only [realMat, pMul, ev_add, ev_multiply, Matrix.mul_apply, Fin.sum_univ_four]
  ring

/-- Coefficient-sum Frobenius square: a rational upper bound of `Σ (Pᵢⱼ(t))²`
uniform in `t` over `[-h, h]`. -/
def matSumSq (P : PolyMat) (h : ℚ) : ℚ := ∑ i, ∑ j, (bound (P i j) h)^2

/-- A rational square witness on the coefficient sums bounds the real
Frobenius norm on the step. -/
theorem matSumSq_frob (P : PolyMat) {t : ℝ} {h : ℚ} (ht : |t| ≤ (h:ℝ)) (B : ℚ)
    (hB : matSumSq P h ≤ B^2) (hB0 : 0 ≤ B) : frob (realMat P t) ≤ (B : ℝ) := by
  refine frob_le_of_sq _ ?_ (by exact_mod_cast hB0)
  have hle : ∑ i, ∑ j, (realMat P t i j)^2 ≤ ∑ i, ∑ j, ((bound (P i j) h : ℚ) : ℝ)^2 := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hev : |ev (P i j) t| ≤ ((bound (P i j) h : ℚ) : ℝ) := ev_abs_le _ ht
    simp only [realMat]; nlinarith [abs_nonneg (ev (P i j) t), sq_abs (ev (P i j) t),
      (abs_nonneg (ev (P i j) t)).trans hev]
  refine hle.trans ?_
  have hcast : (∑ i, ∑ j, ((bound (P i j) h : ℚ) : ℝ)^2)
      = ((matSumSq P h : ℚ) : ℝ) := by unfold matSumSq; push_cast; ring
  rw [hcast]
  calc ((matSumSq P h : ℚ) : ℝ) ≤ ((B^2 : ℚ) : ℝ) := by exact_mod_cast hB
    _ = (B:ℝ)^2 := by push_cast; ring


/-! ### Constant-term evaluation and the symplectic transpose -/

theorem ev_zero (cs : List ℚ) : ev cs 0 = (cs.headI : ℝ) := by
  cases cs with
  | nil => rw [ev_nil, List.headI, show (default : ℚ) = 0 from rfl, Rat.cast_zero]
  | cons a rest => simp [ev_cons, List.headI]

/-- Negate a polynomial. -/
def pNeg (p : List ℚ) : List ℚ := scale (-1) p

theorem ev_pNeg (p : List ℚ) (t : ℝ) : ev (pNeg p) t = - ev p t := by
  unfold pNeg ev; rw [scale_map, evaluate_scale]; simp

/-- The symplectic transpose `H = -J Gᵀ J` of the transition candidate,
still a matrix of rational polynomials. -/
def hMat (G : PolyMat) : PolyMat := fun i j =>
  ![![G 2 2, G 3 2, pNeg (G 0 2), pNeg (G 1 2)],
    ![G 2 3, G 3 3, pNeg (G 0 3), pNeg (G 1 3)],
    ![pNeg (G 2 0), pNeg (G 3 0), G 0 0, G 1 0],
    ![pNeg (G 2 1), pNeg (G 3 1), G 0 1, G 1 1]] i j

/-- The polynomial gradient candidate `Â = [[0, I], [-û³ I + 3 û⁵ q̂ q̂ᵀ, 0]]`. -/
def Ahat (c : Candidate) : PolyMat :=
  let u5 := multiply c.u3 (multiply c.u c.u)
  fun i j =>
    ![![[], [], [1], []],
      ![[], [], [], [1]],
      ![subtract (scale 3 (multiply u5 (multiply c.x c.x))) c.u3,
        scale 3 (multiply u5 (multiply c.x c.y)), [], []],
      ![scale 3 (multiply u5 (multiply c.y c.x)),
        subtract (scale 3 (multiply u5 (multiply c.y c.y))) c.u3, [], []]] i j

/-- Left multiplication by a constant rational matrix (for node kernels). -/
def cMul (C : Matrix (Fin 4) (Fin 4) ℚ) (P : PolyMat) : PolyMat := fun i j =>
  add (scale (C i 0) (P 0 j)) (add (scale (C i 1) (P 1 j))
    (add (scale (C i 2) (P 2 j)) (scale (C i 3) (P 3 j))))

theorem realMat_cMul (C : Matrix (Fin 4) (Fin 4) ℚ) (P : PolyMat) (t : ℝ) :
    realMat (cMul C P) t = (C.map (Rat.castHom ℝ)) * realMat P t := by
  ext i j
  simp only [realMat, cMul, ev_add, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply]
  have hs : ∀ (q : ℚ) (p : List ℚ), ev (scale q p) t = (Rat.castHom ℝ) q * ev p t := by
    intro q p; unfold ev; rw [scale_map, evaluate_scale]
  rw [hs, hs, hs, hs]; ring

/-- Restrict a polynomial matrix to its velocity columns (columns 2, 3). -/
def velCols (P : PolyMat) : PolyMat := fun i j => if j = 2 ∨ j = 3 then P i j else []

/-! ### The curvature candidate and its rational certificate -/

/-- A curvature (transition-matrix) candidate: a polynomial position candidate
together with a polynomial transition matrix `G = Ψ` (with `Ψ(0) = I`) and the
rational bounds consumed by the transported certificate. -/
structure CurvatureCandidate extends Candidate where
  /-- The 16 polynomial entries of the local transition matrix `Ψ`. -/
  G : PolyMat
  /-- Bound of `sup ‖1 - Ψ H‖`. -/
  epsI : ℚ
  /-- Bound of `sup ‖H' + H Â‖`. -/
  epsH : ℚ
  /-- Bound of `sup ‖Ψ‖`. -/
  gSup : ℚ
  /-- Bound of `sup ‖H‖`. -/
  hSup : ℚ
  /-- Bound of `sup ‖H` restricted to its velocity columns`‖`. -/
  kV : ℚ
  /-- Bound of the gradient candidate error `sup ‖Dg - Â_lower‖`. -/
  epsA : ℚ
  /-- Radius of the displacement tube. -/
  Mtube : ℚ

namespace CurvatureCandidate

/-- The symplectic-transpose transition matrix. -/
def H (cc : CurvatureCandidate) : PolyMat := hMat cc.G
/-- The residual `1 - Ψ H`. -/
def residI (cc : CurvatureCandidate) : PolyMat := pSub pId (pMul cc.G cc.H)
/-- The residual `H' + H Â`. -/
def residH (cc : CurvatureCandidate) : PolyMat := pAdd (pDeriv cc.H) (pMul cc.H (Ahat cc.toCandidate))

/-- The decidable rational hypotheses of the curvature certificate. Every
clause is either a base validity condition or a rational inequality that a
finite computation checks; together they imply the real bounds consumed by
the transported certificate. -/
def Valid (cc : CurvatureCandidate) : Prop :=
  cc.toCandidate.Valid ∧ 0 < cc.rhoMin ∧ cc.Mtube < cc.rhoMin ∧ 0 ≤ cc.Mtube ∧
  (∀ i j, (cc.G i j).headI = if i = j then (1:ℚ) else 0) ∧
  0 ≤ cc.epsI ∧ matSumSq cc.residI cc.h ≤ cc.epsI^2 ∧
  0 ≤ cc.gSup ∧ matSumSq cc.G cc.h ≤ cc.gSup^2 ∧
  0 ≤ cc.hSup ∧ matSumSq cc.H cc.h ≤ cc.hSup^2 ∧
  0 ≤ cc.epsH ∧ matSumSq cc.residH cc.h ≤ cc.epsH^2 ∧
  0 ≤ cc.kV ∧ matSumSq (velCols cc.H) cc.h ≤ cc.kV^2 ∧
  0 ≤ cc.epsA ∧ GNC.PlanarCoast.epsA cc.toCandidate ≤ cc.epsA

instance (cc : CurvatureCandidate) : Decidable cc.Valid := by unfold Valid; infer_instance

/-- Soundness of a node kernel bound: a constant matrix `C` times a polynomial
matrix keeps a coefficient-sum Frobenius bound. -/
theorem const_mul_bound_sound (C : Matrix (Fin 4) (Fin 4) ℚ) (P : PolyMat)
    {t : ℝ} {h : ℚ} (ht : |t| ≤ (h:ℝ)) (B : ℚ) (hB : matSumSq (cMul C P) h ≤ B^2)
    (hB0 : 0 ≤ B) : frob ((C.map (Rat.castHom ℝ)) * realMat P t) ≤ (B : ℝ) := by
  have hb := matSumSq_frob (cMul C P) ht B hB hB0
  rwa [realMat_cMul] at hb

section Sound
variable (cc : CurvatureCandidate) (hv : cc.Valid)
include hv

/-- `Ψ(0) = I`. -/
theorem G_zero : realMat cc.G 0 = 1 := by
  ext i j
  rw [realMat, ev_zero, hv.2.2.2.2.1 i j]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- `H(0) = I`. -/
theorem H_zero : realMat cc.H 0 = 1 := by
  have hGe : ∀ k l, ev (cc.G k l) 0 = if k = l then (1:ℝ) else 0 := by
    intro k l
    have h := congrFun (congrFun (G_zero cc hv) k) l
    simpa [realMat, Matrix.one_apply] using h
  ext i j
  simp only [CurvatureCandidate.H, realMat, hMat]
  fin_cases i <;> fin_cases j <;>
    simp [ev_pNeg, hGe]

/-- Soundness of `epsI`: on the step, `‖1 - Ψ(t) H(t)‖ ≤ epsI`. -/
theorem epsI_sound {t : ℝ} (ht : t ∈ Icc (0:ℝ) cc.h) :
    frob (1 - realMat cc.G t * realMat cc.H t) ≤ (cc.epsI : ℝ) := by
  have hb := matSumSq_frob cc.residI (step_abs ht) cc.epsI hv.2.2.2.2.2.2.1 hv.2.2.2.2.2.1
  rwa [residI, realMat_sub, realMat_id, realMat_mul] at hb

/-- Soundness of `gSup`: on the step, `‖Ψ(t)‖ ≤ gSup`. -/
theorem gSup_sound {t : ℝ} (ht : t ∈ Icc (0:ℝ) cc.h) :
    frob (realMat cc.G t) ≤ (cc.gSup : ℝ) :=
  matSumSq_frob cc.G (step_abs ht) cc.gSup hv.2.2.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2.1

/-- Soundness of `hSup`: on the step, `‖H(t)‖ ≤ hSup`. -/
theorem hSup_sound {t : ℝ} (ht : t ∈ Icc (0:ℝ) cc.h) :
    frob (realMat cc.H t) ≤ (cc.hSup : ℝ) :=
  matSumSq_frob cc.H (step_abs ht) cc.hSup hv.2.2.2.2.2.2.2.2.2.2.1
    hv.2.2.2.2.2.2.2.2.2.1

/-- Soundness of `epsH`: on the step, `‖H'(t) + H(t) Â(t)‖ ≤ epsH`. -/
theorem epsH_sound {t : ℝ} (ht : t ∈ Icc (0:ℝ) cc.h) :
    frob (realMat (pDeriv cc.H) t + realMat cc.H t * realMat (Ahat cc.toCandidate) t)
      ≤ (cc.epsH : ℝ) := by
  have hb := matSumSq_frob cc.residH (step_abs ht) cc.epsH
    hv.2.2.2.2.2.2.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2.2.2.2.2.1
  rwa [residH, realMat_add, realMat_mul] at hb

/-- Soundness of `kV`: on the step, the velocity columns of `H(t)` have
Frobenius norm at most `kV`. -/
theorem kV_sound {t : ℝ} (ht : t ∈ Icc (0:ℝ) cc.h) :
    frob (realMat (velCols cc.H) t) ≤ (cc.kV : ℝ) :=
  matSumSq_frob (velCols cc.H) (step_abs ht) cc.kV
    hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Soundness of `epsA`: on the step, `‖Dg(q̂(t)) - Â_lower(t)‖ ≤ epsA`. -/
theorem epsA_sound {t : ℝ} (ht : t ∈ Icc (0:ℝ) cc.h) :
    frob (Dg (cc.toCandidate.pos t) - Alower cc.toCandidate t) ≤ (cc.epsA : ℝ) := by
  refine (gradient_candidate_error cc.toCandidate hv.1 hv.2.1 ht).trans ?_
  exact_mod_cast hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Sound

end CurvatureCandidate

/-! ### A decidable degree-two example -/

/-- A constant Hamiltonian generator `A₀ = [[0, I], [-I, 0]]`. -/
def exA0 : PolyMat := fun i j =>
  ![![[], [], [1], []],
    ![[], [], [], [1]],
    ![[-1], [], [], []],
    ![[], [-1], [], []]] i j

/-- The degree-two transition candidate `Ψ = I + t A₀`. -/
def exG : PolyMat := pAdd pId (fun i j => multiply [0, 1] (exA0 i j))

/-- The constant terms of `Ψ = I + t A₀` form the identity. -/
example : (∀ i j, (exG i j).headI = if i = j then (1:ℚ) else 0) := by decide +kernel

/-- The transition residual `1 - Ψ H` of `Ψ = I + t A₀` is small on the step. -/
example : matSumSq (pSub pId (pMul exG (hMat exG))) (1/10) ≤ (1/10)^2 := by decide +kernel

end GNC.PlanarCoast
