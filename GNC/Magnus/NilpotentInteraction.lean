import GNC.Lie.AffineExponential
import GNC.Magnus.MagnusFlow

/-! Exact interaction propagation for an upper triangular linear system.
After removing the two diagonal fundamental flows, ALL cross-time products
of the remaining generators vanish. This proves the actual exponential and
ODE solution, without assuming convergence of a formal Magnus series.
The orbital specialization uses m = position + velocity and n = attitude.
The diagonal gravity dynamics need not be nilpotent or constant. -/
noncomputable section
open Matrix NormedSpace MeasureTheory
open scoped Matrix.Norms.Operator
namespace GNC.NilpotentInteraction
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def lift (U : Matrix m n ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  fromBlocks 0 U 0 0

omit [DecidableEq m] [DecidableEq n] in
/-- Cross-time annihilation is stronger than the square of each sample vanishing. -/
theorem cross_product (U V : Matrix m n ℝ) : lift U * lift V = 0 := by
  simp [lift, fromBlocks_multiply, fromBlocks_zero]

omit [DecidableEq m] [DecidableEq n] in
theorem cross_commutator (U V : Matrix m n ℝ) :
    lift U * lift V - lift V * lift U = 0 := by rw [cross_product, cross_product, sub_self]

/-- The actual mathlib exponential terminates at degree one. -/
theorem exponential (U : Matrix m n ℝ) : exp (lift U) = fromBlocks 1 U 0 1 :=
  AffineExponential.pure_translation U

theorem conjugate (F : (Matrix m m ℝ)ˣ) (Q : (Matrix n n ℝ)ˣ)
    (K : Matrix m n ℝ) :
    fromBlocks (F⁻¹).val 0 0 (Q⁻¹).val * lift K * fromBlocks F.val 0 0 Q.val =
      lift ((F⁻¹).val * K * Q.val) := by
  simp [lift, fromBlocks_multiply]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem rectangular_derivative {p : Type*} [Fintype p]
    {U : ℝ → Matrix m n ℝ} {V : ℝ → Matrix n p ℝ}
    {U' : Matrix m n ℝ} {V' : Matrix n p ℝ} {t : ℝ}
    (hU : HasDerivAt U U' t) (hV : HasDerivAt V V' t) :
    HasDerivAt (fun s => U s * V s) (U' * V t + U t * V') t := by
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  convert
    HasDerivAt.sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hU i) k).mul
        (hasDerivAt_pi.mp (hasDerivAt_pi.mp hV k) j)) using 1
  · ext s; simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, Finset.sum_add_distrib]

omit [DecidableEq m] [DecidableEq n] in
theorem blocks_derivative
    {F : ℝ → Matrix m m ℝ} {U : ℝ → Matrix m n ℝ} {Q : ℝ → Matrix n n ℝ}
    {F' : Matrix m m ℝ} {U' : Matrix m n ℝ} {Q' : Matrix n n ℝ} {t : ℝ}
    (hF : HasDerivAt F F' t) (hU : HasDerivAt U U' t) (hQ : HasDerivAt Q Q' t) :
    HasDerivAt (fun s => fromBlocks (F s) (U s) 0 (Q s))
      (fromBlocks F' U' 0 Q') t := by
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  rcases i with i | i <;> rcases j with j | j
  · exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hF i) j
  · exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hU i) j
  · exact hasDerivAt_const t 0
  · exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hQ i) j

def primitive (L : ℝ → Matrix m n ℝ) (t : ℝ) : Matrix m n ℝ := ∫ s in (0:ℝ)..t, L s

def liftLinear : Matrix m n ℝ →ₗ[ℝ] Matrix (m ⊕ n) (m ⊕ n) ℝ where
  toFun := lift
  map_add' U V := by simp [lift, fromBlocks_add]
  map_smul' r U := by simp [lift, fromBlocks_smul]

/-- The finite exponent is exactly the first Magnus integral of the transformed generator. -/
theorem first_magnus (L : ℝ → Matrix m n ℝ) (hL : Continuous L) (t : ℝ) :
    (∫ s in (0:ℝ)..t, lift (L s)) = lift (primitive L t) := by
  exact liftLinear.toContinuousLinearMap.intervalIntegral_comp_comm
    (hL.intervalIntegrable (μ := volume) 0 t)

omit [DecidableEq m] [DecidableEq n] in
theorem primitive_derivative (L : ℝ → Matrix m n ℝ) (hL : Continuous L) (t : ℝ) :
    HasDerivAt (primitive L) (L t) t :=
  intervalIntegral.integral_hasDerivAt_right (hL.intervalIntegrable 0 t)
    hL.aestronglyMeasurable.stronglyMeasurableAtFilter hL.continuousAt

/-- One exact quadrature is the entire interaction flow, for arbitrary continuous L. -/
theorem interaction_derivative (L : ℝ → Matrix m n ℝ) (hL : Continuous L) (t : ℝ) :
    HasDerivAt (fun s => exp (lift (primitive L s)))
      (lift (L t) * exp (lift (primitive L t))) t := by
  simp only [exponential]
  convert blocks_derivative (hasDerivAt_const t (1 : Matrix m m ℝ))
    (primitive_derivative L hL t) (hasDerivAt_const t (1 : Matrix n n ℝ)) using 1
  simp [lift, fromBlocks_multiply]

def coefficient (F : ℝ → (Matrix m m ℝ)ˣ) (Q : ℝ → (Matrix n n ℝ)ˣ)
    (K : ℝ → Matrix m n ℝ) (t : ℝ) : Matrix m n ℝ := ((F t)⁻¹).val * K t * (Q t).val

def flow (F : ℝ → (Matrix m m ℝ)ˣ) (Q : ℝ → (Matrix n n ℝ)ˣ)
    (K : ℝ → Matrix m n ℝ) (t : ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  fromBlocks ((F t).val) (((F t).val) * primitive (coefficient F Q K) t) 0 ((Q t).val)

theorem coefficient_continuous (F : ℝ → (Matrix m m ℝ)ˣ)
    (Q : ℝ → (Matrix n n ℝ)ˣ) (T : ℝ → Matrix m m ℝ) (H : ℝ → Matrix n n ℝ)
    (K : ℝ → Matrix m n ℝ)
    (hF : ∀ t, HasDerivAt (fun s => (↑(F s) : Matrix m m ℝ)) (T t * (F t).val) t)
    (hQ : ∀ t, HasDerivAt (fun s => (↑(Q s) : Matrix n n ℝ)) (H t * (Q t).val) t)
    (hK : Continuous K) : Continuous (coefficient F Q K) := by
  have hi : Continuous (fun s => ((F s)⁻¹).val) := by
    apply continuous_iff_continuousAt.mpr; intro t
    have hd := (hasFDerivAt_ringInverse (𝕜 := ℝ) (F t)).comp_hasDerivAt t (hF t)
    change HasDerivAt (fun s => Ring.inverse (F s).val) _ t at hd
    simp only [Ring.inverse_unit] at hd
    exact hd.continuousAt
  exact (hi.matrix_mul hK).matrix_mul
    (continuous_iff_continuousAt.mpr fun t => (hQ t).continuousAt)

/-- Exact solution of the original coupled ODE; the gravity block is retained. -/
theorem flow_derivative (F : ℝ → (Matrix m m ℝ)ˣ)
    (Q : ℝ → (Matrix n n ℝ)ˣ) (T : ℝ → Matrix m m ℝ) (H : ℝ → Matrix n n ℝ)
    (K : ℝ → Matrix m n ℝ)
    (hF : ∀ t, HasDerivAt (fun s => (↑(F s) : Matrix m m ℝ)) (T t * (F t).val) t)
    (hQ : ∀ t, HasDerivAt (fun s => (↑(Q s) : Matrix n n ℝ)) (H t * (Q t).val) t)
    (hK : Continuous K) (t : ℝ) :
    HasDerivAt (flow F Q K) (fromBlocks (T t) (K t) 0 (H t) * flow F Q K t) t := by
  have hp := primitive_derivative _ (coefficient_continuous F Q T H K hF hQ hK) t
  convert blocks_derivative (hF t) (rectangular_derivative (hF t) hp) (hQ t) using 1
  simp [flow, coefficient, fromBlocks_multiply, Matrix.mul_assoc]

theorem flow_initial (F : ℝ → (Matrix m m ℝ)ˣ) (Q : ℝ → (Matrix n n ℝ)ˣ)
    (K : ℝ → Matrix m n ℝ) (hF : F 0 = 1) (hQ : Q 0 = 1) : flow F Q K 0 = 1 := by
  simp [flow, primitive, hF, hQ, fromBlocks_one]

/-- With no thrust coupling, attitude uncertainty has no translational effect
in this retained model. The factorization creates no extra coasting accuracy. -/
theorem flow_zero_coupling (F : ℝ → (Matrix m m ℝ)ˣ) (Q : ℝ → (Matrix n n ℝ)ˣ)
    (t : ℝ) : flow F Q (fun _ => 0) t = fromBlocks (F t).val 0 0 (Q t).val := by
  simp [flow, coefficient, primitive]

theorem flow_factorization (F : ℝ → (Matrix m m ℝ)ˣ) (Q : ℝ → (Matrix n n ℝ)ˣ)
    (K : ℝ → Matrix m n ℝ) (t : ℝ) :
    flow F Q K t = fromBlocks ((F t).val) 0 0 ((Q t).val) *
      exp (lift (primitive (coefficient F Q K) t)) := by
  simp [flow, exponential, fromBlocks_multiply]

/-- With exact diagonal flows, quadrature defect is the only propagation defect
in the attitude-to-translation block. No omitted Magnus commutator is present. -/
theorem quadrature_defect (F : ℝ → (Matrix m m ℝ)ˣ)
    (Q : ℝ → (Matrix n n ℝ)ˣ) (K : ℝ → Matrix m n ℝ) (U : ℝ → Matrix m n ℝ)
    {T : Matrix m m ℝ} {H : Matrix n n ℝ} {E : Matrix m n ℝ} {t : ℝ}
    (hF : HasDerivAt (fun s => (F s).val) (T * (F t).val) t)
    (hQ : HasDerivAt (fun s => (Q s).val) (H * (Q t).val) t)
    (hU : HasDerivAt U (coefficient F Q K t + E) t) :
    HasDerivAt (fun s => fromBlocks (F s).val ((F s).val * U s) 0 (Q s).val)
      (fromBlocks T (K t) 0 H * fromBlocks (F t).val ((F t).val * U t) 0 (Q t).val +
        lift ((F t).val * E)) t := by
  convert blocks_derivative hF (rectangular_derivative hF hU) hQ using 1
  simp [coefficient, lift, fromBlocks_multiply, fromBlocks_add, Matrix.mul_assoc,
    Matrix.mul_add, add_assoc]

/-- Endpoint quadrature error is amplified only by the diagonal flow.
This uses the actual exponential and any common fixed matrix-norm scaling. -/
theorem quadrature_error (D : Matrix (m ⊕ n) (m ⊕ n) ℝ) (U V : Matrix m n ℝ) :
    ‖D * exp (lift U) - D * exp (lift V)‖ ≤ ‖D‖ * ‖lift (U - V)‖ := by
  have he : exp (lift U) - exp (lift V) = lift (U - V) := by
    rw [exponential, exponential]
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [lift]
  rw [← Matrix.mul_sub, he]
  exact norm_mul_le D (lift (U - V))

/-- No existence assumption for the diagonal flows is necessary for continuous inputs. -/
theorem exists_factored_solution (T : ℝ → Matrix m m ℝ) (H : ℝ → Matrix n n ℝ)
    (K : ℝ → Matrix m n ℝ) (hT : Continuous T) (hH : Continuous H) (hK : Continuous K) :
    ∃ F : ℝ → (Matrix m m ℝ)ˣ, ∃ Q : ℝ → (Matrix n n ℝ)ˣ,
      F 0 = 1 ∧ Q 0 = 1 ∧ flow F Q K 0 = 1 ∧
      (∀ t, HasDerivAt (fun s => (↑(F s) : Matrix m m ℝ)) (T t * (F t).val) t) ∧
      (∀ t, HasDerivAt (fun s => (↑(Q s) : Matrix n n ℝ)) (H t * (Q t).val) t) ∧
      ∀ t, HasDerivAt (flow F Q K) (fromBlocks (T t) (K t) 0 (H t) * flow F Q K t) t := by
  obtain ⟨F,hF0,hF⟩ := LinearODE.exists_unit_solution T hT
  obtain ⟨Q,hQ0,hQ⟩ := LinearODE.exists_unit_solution H hH
  exact ⟨F,Q,hF0,hQ0,flow_initial F Q K hF0 hQ0,hF,hQ,
    flow_derivative F Q T H K hF hQ hK⟩

/-- Uniqueness identifies this construction with any independently computed STM. -/
theorem solution_unique (T : ℝ → Matrix m m ℝ) (H : ℝ → Matrix n n ℝ)
    (K : ℝ → Matrix m n ℝ) (hT : Continuous T) (hH : Continuous H) (hK : Continuous K)
    (X Y : ℝ → Matrix (m ⊕ n) (m ⊕ n) ℝ)
    (hX : ∀ t, HasDerivAt X (fromBlocks (T t) (K t) 0 (H t) * X t) t)
    (hY : ∀ t, HasDerivAt Y (fromBlocks (T t) (K t) 0 (H t) * Y t) t)
    (h0 : X 0 = Y 0) : X = Y := by
  have hc : Continuous (fun t => fromBlocks (T t) (K t) 0 (H t)) := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    rcases i with i | i <;> rcases j with j | j
    · exact (continuous_apply j).comp ((continuous_apply i).comp hT)
    · exact (continuous_apply j).comp ((continuous_apply i).comp hK)
    · exact continuous_const
    · exact (continuous_apply j).comp ((continuous_apply i).comp hH)
  exact Magnus.mixed_flow_unique _ (fun _ => 0) hc continuous_const X Y
    (fun t => by simpa using hX t) (fun t => by simpa using hY t) h0

end GNC.NilpotentInteraction
