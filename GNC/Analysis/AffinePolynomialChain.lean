import GNC.Analysis.AffinePolynomialStep

/-! Affine response certificates across a polynomial mesh. Both response
jumps and changes in the approximate coefficient functions are permitted.
The true trajectory and coefficients are shared by the entire chain. -/
namespace GNC.AffinePolynomialStep
open PolynomialODE PolynomialOrder Set
variable {n : ℕ}

/-- Reuse the existing polynomial handoff theorem. No nonlinear-field
validity is asserted for this record projection. -/
def Step.polynomialStep (s : Step n) : PolynomialODE.Step n where
  coefficients := s.coefficients
  duration := s.duration
  region := 0
  lipschitz := s.lipschitz
  initialError := s.initialError
  error := s.error
  defect := s.defect

def Compatible (s next : Step n) : Prop :=
  PolynomialODE.Compatible s.polynomialStep next.polynomialStep
instance (s next : Step n) : Decidable (Compatible s next) := by
  unfold Compatible
  infer_instance

theorem chain_sound (S : ℕ → Step n) (N : ℕ) {h : ℚ}
    (hh : 0≤h) (hvalid : ∀ j<N, (S j).Valid)
    (hduration : ∀ j<N, (S j).duration=h)
    (hjoin : ∀ j, j+1<N → Compatible (S j) (S (j+1)))
    (A : ℝ → Fin n → Fin n → ℝ) (f x : ℝ → Fin n → ℝ) (hx : Continuous x)
    (hd : ∀ t ∈ Icc (0:ℝ) ((N:ℝ)*h),
      HasDerivAt x (fun i => (∑ k, A t i k*x t k)+f t i) t)
    (hA : ∀ j<N, ∀ t ∈ Icc (0:ℝ) h, ∀ i k,
      |A ((j:ℝ)*h+t) i k-value ((S j).operator i k) t|≤((S j).operatorError:ℝ))
    (hf : ∀ j<N, ∀ t ∈ Icc (0:ℝ) h, ∀ i,
      |f ((j:ℝ)*h+t) i-value ((S j).input i) t|≤((S j).inputError:ℝ))
    (hi : ‖x 0-curve (S 0).coefficients 0‖≤((S 0).initialError:ℝ)) :
    ∀ j<N, ∀ t ∈ Icc (0:ℝ) h,
      ‖x ((j:ℝ)*h+t)-curve (S j).coefficients t‖<((S j).error:ℝ) := by
  have hhr : (0:ℝ)≤h := by exact_mod_cast hh
  intro j
  induction j with
  | zero =>
    intro hj t ht
    have htN : ∀ u ∈ Icc (0:ℝ) (S 0).duration, u ∈ Icc (0:ℝ) ((N:ℝ)*h) := by
      intro u hu
      rw [hduration 0 hj] at hu
      have hN : (1:ℝ)≤N := by exact_mod_cast hj
      exact ⟨hu.1,hu.2.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hN) hhr])⟩
    have hb := step_sound (S 0) (hvalid 0 hj) A f x hx
      (fun u hu => hd u (htN u hu))
      (fun u hu i k => by simpa using hA 0 hj u (by simpa [hduration 0 hj] using hu) i k)
      (fun u hu i => by simpa using hf 0 hj u (by simpa [hduration 0 hj] using hu) i)
      hi t (by simpa [hduration 0 hj] using ht)
    simpa using hb
  | succ j ih =>
    intro hj t ht
    have hj' : j<N := Nat.lt_of_succ_lt hj
    have hprev := ih hj' (h:ℝ) ⟨hhr,le_rfl⟩
    have htime : (j:ℝ)*h+(h:ℝ)=((j+1:ℕ):ℝ)*h := by push_cast; ring
    rw [htime] at hprev
    have hnext := PolynomialODE.handoff (S j).polynomialStep (S (j+1)).polynomialStep
      (hjoin j hj) (hvalid (j+1) hj).2.1 (x (((j+1:ℕ):ℝ)*h))
      (by simpa [Step.polynomialStep,hduration j hj'] using hprev.le)
    let shifted := fun u : ℝ => x (((j+1:ℕ):ℝ)*h+u)
    have hshift : Continuous shifted := hx.comp (continuous_const.add continuous_id)
    have hder : ∀ u ∈ Icc (0:ℝ) (S (j+1)).duration,
        HasDerivAt shifted
          (fun i => (∑ k, A (((j+1:ℕ):ℝ)*h+u) i k*shifted u k)+
            f (((j+1:ℕ):ℝ)*h+u) i) u := by
      intro u hu
      rw [hduration (j+1) hj] at hu
      have hjr : ((j+1:ℕ):ℝ)+1≤N := by exact_mod_cast hj
      have hji : (0:ℝ)≤((j+1:ℕ):ℝ) := by positivity
      have hur : ((j+1:ℕ):ℝ)*h+u ∈ Icc (0:ℝ) ((N:ℝ)*h) :=
        ⟨add_nonneg (mul_nonneg hji hhr) hu.1,
          by nlinarith [mul_nonneg (sub_nonneg.mpr hjr) hhr,hu.2]⟩
      simpa [shifted] using (hd _ hur).scomp u
        ((hasDerivAt_id u).const_add (((j+1:ℕ):ℝ)*h))
    exact step_sound (S (j+1)) (hvalid (j+1) hj)
      (fun u => A (((j+1:ℕ):ℝ)*h+u)) (fun u => f (((j+1:ℕ):ℝ)*h+u))
      shifted hshift hder
      (fun u hu => hA (j+1) hj u (by simpa [hduration (j+1) hj] using hu))
      (fun u hu => hf (j+1) hj u (by simpa [hduration (j+1) hj] using hu))
      (by simpa [Step.polynomialStep,shifted] using hnext)
      t (by simpa [hduration (j+1) hj] using ht)

end GNC.AffinePolynomialStep
