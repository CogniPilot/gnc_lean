import GNC.Analysis.BallNormProfile
import GNC.Analysis.TruncatedProduct

/-! Executable polynomial enclosure arithmetic on a three-dimensional ball.
Each block carries a checked scalar range profile. Products outside the
chosen degree budget are bounded before coefficient multiplication. Degree
tags select the retained pairs; soundness requires an exact partition, not
an assumption that tags correctly describe homogeneous degrees.

All time powers are retained. The multiplication rule includes propagation
of both incoming errors and their product. The rules apply equally to Lie
and Cartesian coordinates, and do not assert validity of any external trace.
-/
namespace GNC.BallPolynomialEnclosure
open ParameterPolynomial

def polynomialSum {n : ℕ} (p : Fin n → Coefficients) : Coefficients :=
  (List.finRange n).foldr (fun i r => add (p i) r) []

def profileSum {n : ℕ} (p : Fin n → List ℚ) : List ℚ :=
  (List.finRange n).foldr (fun i r => PolynomialBounds.add (p i) r) []

structure Block where
  degree : ℕ
  core : Coefficients
  range : DiskTimePolynomial.Certificate 1

def Block.Valid (p : Block) (σ : ℚ) : Prop :=
  BallNormProfile.CertificateValid p.range ![p.core] σ

structure Partition where
  count : ℕ
  blocks : Fin count → Block

def Partition.Valid (p : Partition) (σ : ℚ) : Prop := ∀ i, (p.blocks i).Valid σ

def Partition.core (p : Partition) : Coefficients := polynomialSum fun i => (p.blocks i).core
def Partition.bound (p : Partition) : List ℚ := profileSum fun i => (p.blocks i).range.bound 1

/-- Crucially, the degree test precedes multiplication of the coefficients. -/
def retainedProduct (N : ℕ) (p q : Partition) : Coefficients :=
  polynomialSum fun i => polynomialSum fun j =>
    if (p.blocks i).degree+(q.blocks j).degree≤N then
      multiply (p.blocks i).core (q.blocks j).core else []

def discardedProfile (N : ℕ) (p q : Partition) : List ℚ :=
  profileSum fun i => profileSum fun j =>
    if (p.blocks i).degree+(q.blocks j).degree≤N then [] else
      PolynomialBounds.multiply ((p.blocks i).range.bound 1) ((q.blocks j).range.bound 1)

/-- Discarded core products plus all propagated error terms. -/
def multiplicationError (N : ℕ) (p q : Partition) (E F : List ℚ) : List ℚ :=
  PolynomialBounds.add
    (PolynomialBounds.add
      (PolynomialBounds.add (discardedProfile N p q) (PolynomialBounds.multiply p.bound F))
      (PolynomialBounds.multiply q.bound E))
    (PolynomialBounds.multiply E F)

noncomputable section

/-- Scalar coefficient norms need no repeated rational squaring checks. -/
theorem scalarProfile_valid (p : List ℚ) :
    CoefficientNormProfile.Valid ![p] (p.map abs) := by
  induction p with
  | nil => intro i; fin_cases i; rfl
  | cons a p ih =>
    refine ⟨abs_nonneg a, ?_, ?_⟩
    · simp [sq_abs]
    · have he : (fun i : Fin 1 => (![a::p] i).tail)=![p] := by
        funext i
        fin_cases i
        rfl
      rw [he]
      exact ih

/-- Check a stored scalar profile by list equality, avoiding coefficient
squaring and a second copy of the input coefficients in its proof. -/
theorem checked_scalarProfile (p : DiskPolynomial.Curve 1) (b : List ℚ)
    (hb : b=(p 0).map abs) : CoefficientNormProfile.Valid p b := by
  rw [hb]
  convert scalarProfile_valid (p 0) using 1
  funext i
  fin_cases i
  rfl

theorem polynomialSum_value {n : ℕ} (p : Fin n → Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value (polynomialSum p) x t=∑ i, value (p i) x t := by
  have hf (l : List (Fin n)) :
      value (l.foldr (fun i r => add (p i) r) []) x t=
        (l.map fun i => value (p i) x t).sum := by
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.foldr_cons,value_add,ih,List.map_cons,List.sum_cons]
  rw [polynomialSum,hf]
  rw [←List.sum_toFinset _ (List.nodup_finRange n),List.toFinset_finRange]

theorem profileSum_value {n : ℕ} (p : Fin n → List ℚ) (t : ℝ) :
    PolynomialOrder.value (profileSum p) t=∑ i, PolynomialOrder.value (p i) t := by
  have hf (l : List (Fin n)) :
      PolynomialOrder.value (l.foldr (fun i r => PolynomialBounds.add (p i) r) []) t=
        (l.map fun i => PolynomialOrder.value (p i) t).sum := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldr_cons,PolynomialOrder.value_add,ih,List.map_cons,List.sum_cons]
  rw [profileSum,hf]
  rw [←List.sum_toFinset _ (List.nodup_finRange n),List.toFinset_finRange]

theorem Block.certifies (p : Block) {σ : ℚ} (hp : p.Valid σ) {x : Fin 3 → ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2) {t : ℝ} (ht : 0≤t) :
    |value p.core x t|≤PolynomialOrder.value (p.range.bound 1) t := by
  have hc : |value p.core x t|≤‖DiskPolynomial.vectorValue ![p.core] x t‖ := by
    simpa [DiskPolynomial.vectorValue,Real.norm_eq_abs] using
      PiLp.norm_apply_le (DiskPolynomial.vectorValue ![p.core] x t) (0 : Fin 1)
  exact hc.trans (BallNormProfile.certifies p.range ![p.core] hp hx ht)

theorem Partition.certifies (p : Partition) {σ : ℚ} (hp : p.Valid σ) {x : Fin 3 → ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2) {t : ℝ} (ht : 0≤t) :
    |value p.core x t|≤PolynomialOrder.value p.bound t := by
  rw [Partition.core,polynomialSum_value,Partition.bound,profileSum_value]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => (p.blocks i).certifies (hp i) hx ht)

theorem retainedProduct_value (N : ℕ) (p q : Partition) (x : Fin 3 → ℝ) (t : ℝ) :
    value (retainedProduct N p q) x t=
      ∑ i, ∑ j, if (p.blocks i).degree+(q.blocks j).degree≤N then
        value (p.blocks i).core x t*value (q.blocks j).core x t else 0 := by
  simp only [retainedProduct,polynomialSum_value]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [value_multiply]

theorem discardedProfile_value (N : ℕ) (p q : Partition) (t : ℝ) :
    PolynomialOrder.value (discardedProfile N p q) t=
      ∑ i, ∑ j, if (p.blocks i).degree+(q.blocks j).degree≤N then 0 else
        PolynomialOrder.value ((p.blocks i).range.bound 1) t*
          PolynomialOrder.value ((q.blocks j).range.bound 1) t := by
  simp only [discardedProfile,profileSum_value]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rfl
  · exact DiskPolynomial.value_multiply _ _ t

/-- A checked error bound without forming any omitted coefficient product. -/
theorem truncation_bound (N : ℕ) (p q : Partition) {σ : ℚ}
    (hp : p.Valid σ) (hq : q.Valid σ) {x : Fin 3 → ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2) {t : ℝ} (ht : 0≤t) :
    |value p.core x t*value q.core x t-value (retainedProduct N p q) x t|≤
      PolynomialOrder.value (discardedProfile N p q) t := by
  rw [Partition.core,Partition.core,polynomialSum_value,polynomialSum_value,
    retainedProduct_value,discardedProfile_value]
  exact TruncatedProduct.discarded_pairs Finset.univ Finset.univ
    (fun i => value (p.blocks i).core x t)
    (fun i => PolynomialOrder.value ((p.blocks i).range.bound 1) t)
    (fun j => value (q.blocks j).core x t)
    (fun j => PolynomialOrder.value ((q.blocks j).range.bound 1) t)
    (fun i => (p.blocks i).degree) (fun j => (q.blocks j).degree) N
    (fun i _ => (p.blocks i).certifies (hp i) hx ht)
    (fun j _ => (q.blocks j).certifies (hq j) hx ht)

theorem multiplication_bound (N : ℕ) (p q : Partition) {σ : ℚ}
    (hp : p.Valid σ) (hq : q.Valid σ) {x : Fin 3 → ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2) {t : ℝ} (ht : 0≤t)
    {u v : ℝ} (E F : List ℚ)
    (hu : |u-value p.core x t|≤PolynomialOrder.value E t)
    (hv : |v-value q.core x t|≤PolynomialOrder.value F t) :
    |u*v-value (retainedProduct N p q) x t|≤
      PolynomialOrder.value (multiplicationError N p q E F) t := by
  simpa only [multiplicationError,PolynomialOrder.value_add,DiskPolynomial.value_multiply] using
    TruncatedProduct.multiplication (p.certifies hp hx ht) (q.certifies hq hx ht) hu hv
      (truncation_bound N p q hp hq hx ht)

/-- A producer may canonicalize the retained polynomial and round the error
profile upward. Both changes are checked by exact rational predicates. -/
theorem checked_multiplication (N : ℕ) (p q : Partition) {σ : ℚ}
    (hp : p.Valid σ) (hq : q.Valid σ) (r : Coefficients) (E F R : List ℚ)
    (hcore : zero (subtract (retainedProduct N p q) r))
    (herror : PolynomialOrder.nonnegative
      (PolynomialBounds.subtract R (multiplicationError N p q E F)))
    {x : Fin 3 → ℝ} (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2) {t : ℝ} (ht : 0≤t)
    {u v : ℝ} (hu : |u-value p.core x t|≤PolynomialOrder.value E t)
    (hv : |v-value q.core x t|≤PolynomialOrder.value F t) :
    |u*v-value r x t|≤PolynomialOrder.value R t := by
  have h := multiplication_bound N p q hp hq hx ht E F hu hv
  rw [ParameterPolynomial.identity _ _ hcore x t] at h
  have he := PolynomialOrder.value_nonnegative _ herror ht
  rw [PolynomialOrder.value_subtract] at he
  exact h.trans (sub_nonneg.mp he)

theorem addition_bound (p q : Coefficients) (E F : List ℚ)
    {x : Fin 3 → ℝ} {t u v : ℝ}
    (hu : |u-value p x t|≤PolynomialOrder.value E t)
    (hv : |v-value q x t|≤PolynomialOrder.value F t) :
    |u+v-value (add p q) x t|≤PolynomialOrder.value (PolynomialBounds.add E F) t := by
  rw [value_add,PolynomialOrder.value_add]
  have he : u+v-(value p x t+value q x t)=(u-value p x t)+(v-value q x t) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hu hv)

theorem scaling_bound (a : ℚ) (p : Coefficients) (E : List ℚ)
    {x : Fin 3 → ℝ} {t u : ℝ}
    (hu : |u-value p x t|≤PolynomialOrder.value E t) :
    |(a:ℝ)*u-value (scale a p) x t|≤
      PolynomialOrder.value (PolynomialBounds.scale |a| E) t := by
  rw [value_scale,PolynomialOrder.value_scale,Rat.cast_abs,←mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)

/-- Combine a Euclidean core profile with componentwise enclosure tails.
The scalar tails use an l1 bound, matching the executable proposer. -/
theorem vector_bound {n : ℕ} (p : DiskPolynomial.Vector n)
    (D : DiskTimePolynomial.Certificate n) {σ : ℚ}
    (hD : BallNormProfile.CertificateValid D p σ) (E : Fin n → List ℚ)
    {x : Fin 3 → ℝ} (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2) {t : ℝ} (ht : 0≤t)
    (v : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, |v i-value (p i) x t|≤PolynomialOrder.value (E i) t) :
    ‖v‖≤PolynomialOrder.value (PolynomialBounds.add (D.bound 1) (profileSum E)) t := by
  have hl1 (w : EuclideanSpace ℝ (Fin n)) : ‖w‖≤∑ i, |w i| := by
    let f : Fin n → EuclideanSpace ℝ (Fin n) := fun i => PiLp.single 2 i (w i)
    have he : w=∑ i, f i := by
      ext j
      simp [f]
    calc
      ‖w‖=‖∑ i, f i‖ := congrArg norm he
      _≤∑ i, ‖f i‖ := norm_sum_le _ _
      _=∑ i, |w i| := by simp [f,PiLp.norm_single,Real.norm_eq_abs]
  have he : ‖v-DiskPolynomial.vectorValue p x t‖≤∑ i, PolynomialOrder.value (E i) t := by
    apply (hl1 _).trans
    exact Finset.sum_le_sum fun i _ => hv i
  rw [PolynomialOrder.value_add,profileSum_value]
  have hn : ‖v‖≤‖DiskPolynomial.vectorValue p x t‖+‖v-DiskPolynomial.vectorValue p x t‖ := by
    simpa using norm_add_le (DiskPolynomial.vectorValue p x t) (v-DiskPolynomial.vectorValue p x t)
  exact hn.trans (add_le_add (BallNormProfile.certifies D p hD hx ht) he)

end
end GNC.BallPolynomialEnclosure
