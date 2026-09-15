import GNC.Dynamics.RotatingGravityClosedForm
import GNC.Analysis.BiquadraticSpectrum
import GNC.Analysis.ModalQuadraticResponse

/-! Checked spectral modes of the actual powered rotating gravity blocks.
The zero-thrust HCW limit remains covered by `RotatingGravityClosedForm`;
its zero Jordan block is excluded from this simple-eigenmode construction. -/
noncomputable section
set_option autoImplicit false
namespace GNC.RotatingGravity
open Matrix QuadraticModes BiquadraticSpectrum
open scoped BigOperators

def complexify {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    Matrix n n ℂ := Complex.ofRealHom.mapMatrix M

theorem complexify_smul {n : Type*} [Fintype n] [DecidableEq n]
    (r : ℝ) (M : Matrix n n ℝ) :
    complexify (r • M) = (r : ℂ) • complexify M := by
  ext i j
  simp [complexify]

theorem complexify_pow {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (j : ℕ) : complexify (M^j) = complexify M^j :=
  (Complex.ofRealHom.mapMatrix).map_pow M j

theorem complexify_sub {n : Type*} [Fintype n] [DecidableEq n]
    (M N : Matrix n n ℝ) : complexify (M-N) = complexify M-complexify N :=
  (Complex.ofRealHom.mapMatrix).map_sub M N

theorem complexify_one {n : Type*} [Fintype n] [DecidableEq n] :
    complexify (1 : Matrix n n ℝ) = 1 := (Complex.ofRealHom.mapMatrix).map_one

/-- A complex square root of a real squared frequency, using mathlib's real
square root. This is the positive real or positive imaginary branch. -/
def realSquareRoot (q : ℝ) : ℂ :=
  if 0 ≤ q then (Real.sqrt q : ℂ) else Complex.I*(Real.sqrt (-q) : ℂ)

theorem realSquareRoot_sq (q : ℝ) : realSquareRoot q^2 = (q : ℂ) := by
  by_cases hq : 0 ≤ q
  · simp [realSquareRoot, hq, ← Complex.ofReal_pow, Real.sq_sqrt hq]
  · have hn : 0 ≤ -q := by linarith
    simp [realSquareRoot, hq, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hn]

theorem realSquareRoot_ne_zero {q : ℝ} (hq : q ≠ 0) : realSquareRoot q ≠ 0 := by
  intro h
  have hz : (q : ℂ) = 0 := by rw [← realSquareRoot_sq q, h, zero_pow (by decide)]
  exact hq (Complex.ofReal_eq_zero.mp hz)

theorem complex_planar_biquadratic {k w : ℝ} (hd : 0 ≤ discriminant k w) :
    complexify (planar k w)^4 =
      ((plusRoot k w : ℂ)+(minusRoot k w : ℂ)) • complexify (planar k w)^2 -
      ((plusRoot k w : ℂ)*(minusRoot k w : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h := congrArg complexify (planar_biquadratic hd)
  simpa only [complexify_sub, complexify_smul, complexify_pow, complexify_one,
    Complex.ofReal_add, Complex.ofReal_mul] using h

def planeRate (k w : ℝ) : Fin 4 → ℂ :=
  ![realSquareRoot (plusRoot k w), -realSquareRoot (plusRoot k w),
    realSquareRoot (minusRoot k w), -realSquareRoot (minusRoot k w)]

def planeProjector (k w : ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  let W := complexify (planar k w)
  let p : ℂ := plusRoot k w
  let q : ℂ := minusRoot k w
  ![split W (projector W p q) (realSquareRoot (plusRoot k w)),
    split W (projector W p q) (-realSquareRoot (plusRoot k w)),
    split W (projector W q p) (realSquareRoot (minusRoot k w)),
    split W (projector W q p) (-realSquareRoot (minusRoot k w))]

theorem planeProjector_sum {k w : ℝ} (hk : 0 < k) (hw : w^2 < k) :
    ∑ i, planeProjector k w i = 1 := by
  have hpq : (plusRoot k w : ℂ) ≠ (minusRoot k w : ℂ) := by
    exact_mod_cast roots_distinct hk hw.le
  simpa [planeProjector, Fin.sum_univ_succ, add_assoc] using
    four_modes_sum (complexify (planar k w)) (plusRoot k w) (minusRoot k w)
      (realSquareRoot (plusRoot k w)) (realSquareRoot (minusRoot k w)) hpq

theorem planeProjector_eigen {k w : ℝ} (hk : 0 < k) (hw : w^2 < k) (i : Fin 4) :
    complexify (planar k w)*planeProjector k w i = planeRate k w i • planeProjector k w i := by
  have hs := powered_root_signs hk hw
  have hsp := realSquareRoot_ne_zero (ne_of_gt hs.1)
  have hsq := realSquareRoot_ne_zero (ne_of_lt hs.2)
  have hW := complex_planar_biquadratic (discriminant_positive hk hw.le).le
  have hW' : complexify (planar k w)^4 =
      ((minusRoot k w : ℂ)+(plusRoot k w : ℂ)) • complexify (planar k w)^2 -
      ((minusRoot k w : ℂ)*(plusRoot k w : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    simpa only [add_comm, mul_comm] using hW
  fin_cases i
  · exact projector_eigen _ _ _ _ hW hsp (realSquareRoot_sq _)
  · exact projector_eigen _ _ _ _ hW (neg_ne_zero.mpr hsp) (by rw [neg_sq, realSquareRoot_sq])
  · exact projector_eigen _ _ _ _ hW' hsq (realSquareRoot_sq _)
  · exact projector_eigen _ _ _ _ hW' (neg_ne_zero.mpr hsq) (by rw [neg_sq, realSquareRoot_sq])

def normalRate (k : ℝ) : Fin 2 → ℂ := ![realSquareRoot (-k), -realSquareRoot (-k)]

def normalProjector (k : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![split (complexify (normal k)) 1 (realSquareRoot (-k)),
    split (complexify (normal k)) 1 (-realSquareRoot (-k))]

theorem normalProjector_sum (k : ℝ) : ∑ i, normalProjector k i = 1 := by
  simpa [normalProjector, Fin.sum_univ_succ] using
    split_sum (complexify (normal k)) 1 (realSquareRoot (-k))

theorem normalProjector_eigen {k : ℝ} (hk : 0 < k) (i : Fin 2) :
    complexify (normal k)*normalProjector k i = normalRate k i • normalProjector k i := by
  have hW : complexify (normal k)^2 = (-k : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa only [complexify_smul, complexify_pow, complexify_one, Complex.ofReal_neg] using
      congrArg complexify (normal_relation k)
  have hs := realSquareRoot_ne_zero (neg_ne_zero.mpr (ne_of_gt hk))
  fin_cases i
  · apply split_eigen _ _ _ hs
    simpa [realSquareRoot_sq] using hW
  · apply split_eigen _ _ _ (neg_ne_zero.mpr hs)
    simpa [realSquareRoot_sq] using hW

abbrev SpectrumIndex := Fin 4 ⊕ Fin 2

def spectrumRate (k w : ℝ) : SpectrumIndex → ℂ := Sum.elim (planeRate k w) (normalRate k)

def spectrumGenerator (k w : ℝ) : Matrix SpectrumIndex SpectrumIndex ℂ :=
  fromBlocks (complexify (planar k w)) 0 0 (complexify (normal k))

def spectrumProjector (k w : ℝ) : SpectrumIndex → Matrix SpectrumIndex SpectrumIndex ℂ
  | .inl i => fromBlocks (planeProjector k w i) 0 0 0
  | .inr i => fromBlocks 0 0 0 (normalProjector k i)

theorem spectrumProjector_sum {k w : ℝ} (hk : 0 < k) (hw : w^2 < k) :
    ∑ i, spectrumProjector k w i = 1 := by
  have hp := planeProjector_sum hk hw
  have hn := normalProjector_sum k
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [Fintype.sum_sum_type, spectrumProjector, Matrix.sum_apply, Matrix.one_apply] using congrFun (congrFun hp i) j
  · simp [Fintype.sum_sum_type, spectrumProjector, Matrix.sum_apply]
  · simp [Fintype.sum_sum_type, spectrumProjector, Matrix.sum_apply]
  · simpa [Fintype.sum_sum_type, spectrumProjector, Matrix.sum_apply, Matrix.one_apply] using congrFun (congrFun hn i) j

theorem spectrumProjector_eigen {k w : ℝ} (hk : 0 < k) (hw : w^2 < k) (i : SpectrumIndex) :
    spectrumGenerator k w*spectrumProjector k w i =
      spectrumRate k w i • spectrumProjector k w i := by
  rcases i with i | i
  · simp [spectrumGenerator, spectrumProjector, spectrumRate, fromBlocks_multiply,
      planeProjector_eigen hk hw, fromBlocks_smul]
  · simp [spectrumGenerator, spectrumProjector, spectrumRate, fromBlocks_multiply,
      normalProjector_eigen hk, fromBlocks_smul]

theorem spectrum_map_identity {k w : ℝ} (hk : 0 < k) (hw : w^2 < k)
    (b : SpectrumIndex → ℂ) :
    ∑ i, (Matrix.mulVecLin (spectrumProjector k w i)) b = b := by
  change ∑ i, spectrumProjector k w i *ᵥ b = b
  rw [← Matrix.sum_mulVec, spectrumProjector_sum hk hw, Matrix.one_mulVec]

theorem spectrum_map_eigen {k w : ℝ} (hk : 0 < k) (hw : w^2 < k)
    (i : SpectrumIndex) (b : SpectrumIndex → ℂ) :
    (Matrix.mulVecLin (spectrumGenerator k w))
      ((Matrix.mulVecLin (spectrumProjector k w i)) b) =
      spectrumRate k w i • (Matrix.mulVecLin (spectrumProjector k w i)) b := by
  change spectrumGenerator k w *ᵥ (spectrumProjector k w i *ᵥ b) = _
  rw [Matrix.mulVec_mulVec, spectrumProjector_eigen hk hw, Matrix.smul_mulVec]
  rfl

end GNC.RotatingGravity
