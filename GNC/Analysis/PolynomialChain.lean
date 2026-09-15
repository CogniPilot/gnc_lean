import GNC.Analysis.PolynomialODE

/-! Composition of polynomial ODE step certificates, including discontinuities
between adjacent numerical polynomial proposals. -/
namespace GNC.PolynomialODE
open Planning.PolynomialKernel
variable {n : ℕ}

def Compatible (s next : Step n) : Prop :=
  ∀ i, |evaluate (s.coefficients i) s.duration-evaluate (next.coefficients i) 0|+
    s.error ≤ next.initialError

instance (s next : Step n) : Decidable (Compatible s next) := by
  unfold Compatible
  infer_instance

theorem curve_rational (cs : Fin n → List ℚ) (t : ℚ) (i : Fin n) :
    curve cs (t:ℝ) i = ((evaluate (cs i) t : ℚ):ℝ) :=
  evaluate_map (Rat.castHom ℝ) (cs i) t

theorem handoff (s next : Step n) (h : Compatible s next)
    (he : 0 ≤ next.initialError) (y : Fin n → ℝ)
    (hy : ‖y-curve s.coefficients s.duration‖ ≤ (s.error:ℝ)) :
    ‖y-curve next.coefficients 0‖ ≤ (next.initialError:ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast he)).mpr
  intro i
  have hi := (norm_le_pi_norm (y-curve s.coefficients s.duration) i).trans hy
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hi ⊢
  have hc : |curve s.coefficients s.duration i-curve next.coefficients 0 i|+
      (s.error:ℝ) ≤ next.initialError := by
    have hr := h i
    rw [curve_rational, show (0:ℝ) = ((0:ℚ):ℝ) by norm_num, curve_rational]
    exact_mod_cast hr
  have ht := abs_add_le (y i-curve s.coefficients s.duration i)
    (curve s.coefficients s.duration i-curve next.coefficients 0 i)
  simp only [sub_add_sub_cancel] at ht
  linarith

/-- A finite sequence encloses every real time in every step, including both
endpoints. Polynomial jumps are handled explicitly by `Compatible`. -/
theorem chain_sound (S : ℕ → Step n) (f : Fin n → Expr n) (N : ℕ) {h : ℚ}
    (hh : 0 ≤ h) (hvalid : ∀ j < N, (S j).Valid f)
    (hduration : ∀ j < N, (S j).duration = h)
    (hjoin : ∀ j, j+1 < N → Compatible (S j) (S (j+1)))
    (x : ℝ → Fin n → ℝ) (hx : Continuous x)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) ((N:ℝ)*h), HasDerivAt x (fun i => (f i).value (x t)) t)
    (hi : ‖x 0-curve (S 0).coefficients 0‖ ≤ ((S 0).initialError:ℝ)) :
    ∀ j < N, ∀ t ∈ Set.Icc (0:ℝ) h,
      ‖x ((j:ℝ)*h+t)-curve (S j).coefficients t‖ < ((S j).error:ℝ) := by
  have hhr : (0:ℝ) ≤ h := by exact_mod_cast hh
  intro j
  induction j with
  | zero =>
    intro hj t ht
    have htN : ∀ u ∈ Set.Icc (0:ℝ) (S 0).duration, u ∈ Set.Icc (0:ℝ) ((N:ℝ)*h) := by
      intro u hu
      rw [hduration 0 hj] at hu
      have hN : (1:ℝ) ≤ N := by exact_mod_cast hj
      exact ⟨hu.1, hu.2.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hN) hhr])⟩
    have hb := step_sound (S 0) f (hvalid 0 hj) x hx
      (fun u hu => hd u (htN u hu)) hi t (by simpa [hduration 0 hj] using ht)
    simpa using hb
  | succ j ih =>
    intro hj t ht
    have hj' : j < N := Nat.lt_of_succ_lt hj
    have hprev := ih hj' (h:ℝ) ⟨hhr,le_rfl⟩
    have htime : (j:ℝ)*h+(h:ℝ) = ((j+1:ℕ):ℝ)*h := by push_cast; ring
    rw [htime] at hprev
    have hnext := handoff (S j) (S (j+1)) (hjoin j hj)
      (hvalid (j+1) hj).2.2.2.1 (x (((j+1:ℕ):ℝ)*h))
      (by simpa [hduration j hj'] using hprev.le)
    let shifted := fun u : ℝ => x (((j+1:ℕ):ℝ)*h+u)
    have hshift : Continuous shifted := hx.comp (continuous_const.add continuous_id)
    have hder : ∀ u ∈ Set.Icc (0:ℝ) (S (j+1)).duration,
        HasDerivAt shifted (fun i => (f i).value (shifted u)) u := by
      intro u hu
      rw [hduration (j+1) hj] at hu
      have hjr : ((j+1:ℕ):ℝ)+1 ≤ N := by exact_mod_cast hj
      have hji : (0:ℝ) ≤ ((j+1:ℕ):ℝ) := by positivity
      have hur : ((j+1:ℕ):ℝ)*h+u ∈ Set.Icc (0:ℝ) ((N:ℝ)*h) :=
        ⟨add_nonneg (mul_nonneg hji hhr) hu.1,
          by nlinarith [mul_nonneg (sub_nonneg.mpr hjr) hhr, hu.2]⟩
      simpa [shifted] using (hd _ hur).scomp u
        ((hasDerivAt_id u).const_add (((j+1:ℕ):ℝ)*h))
    exact step_sound (S (j+1)) f (hvalid (j+1) hj) shifted hshift hder
      (by simpa [shifted] using hnext) t (by simpa [hduration (j+1) hj] using ht)

theorem grid_covers (N : ℕ) {h t : ℝ} (hh : 0 ≤ h) (hN : 0 < N)
    (ht : t ∈ Set.Icc 0 ((N:ℝ)*h)) :
    ∃ j < N, ∃ u ∈ Set.Icc 0 h, t = (j:ℝ)*h+u := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hzero : N = 0
    · subst N
      exact ⟨0, by omega, t, by simpa using ht, by simp⟩
    by_cases hprefix : t ≤ (N:ℝ)*h
    · obtain ⟨j,hj,u,hu,he⟩ := ih (by omega) ⟨ht.1,hprefix⟩
      exact ⟨j, by omega, u, hu, he⟩
    · refine ⟨N, by omega, t-(N:ℝ)*h, ⟨by linarith, ?_⟩, by ring⟩
      have hb := ht.2
      push_cast at hb
      nlinarith

end GNC.PolynomialODE
