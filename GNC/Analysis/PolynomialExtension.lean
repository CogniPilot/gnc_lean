import GNC.Analysis.PolynomialChain
import GNC.Analysis.ClippedPolynomial

/-! Polynomial certificates also prove existence. First the step error
argument is localized to the certified cube. This permits a bounded extension
of the field; its solution is then proved to stay where the extension agrees
with the original polynomial dynamics.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.PolynomialODE
open Planning.PolynomialKernel Set
open scoped NNReal
variable {n : ℕ}

theorem region_of_enclosure (s : Step n) (f : Fin n → Expr n) (hs : s.Valid f)
    {y : Fin n → ℝ} {t : ℝ} (ht : t ∈ Icc (0:ℝ) s.duration)
    (hy : ‖y-curve s.coefficients t‖ < (s.error:ℝ)) (i : Fin n) :
    |y i| < (s.region:ℝ) := by
  have hcheck := hs.2.2.2.2.2.2.2 i
  have hp := PolynomialBounds.bound_sound (s.coefficients i)
    (show |t| ≤ (s.duration:ℝ) by rw [abs_of_nonneg ht.1]; exact ht.2)
  have he := (norm_le_pi_norm (y-curve s.coefficients t) i).trans_lt hy
  have hb : (PolynomialBounds.bound (s.coefficients i) s.duration:ℝ)+s.error ≤ s.region :=
    by exact_mod_cast hcheck.1
  have ha := abs_add_le (y i-curve s.coefficients t i) (curve s.coefficients t i)
  simp only [sub_add_cancel] at ha
  simp only [Pi.sub_apply, Real.norm_eq_abs] at he
  change |curve s.coefficients t i| ≤ _ at hp
  linarith

/-- Only the derivative inside the certified state cube is needed. The
first-exit argument proves the required cube membership along the solution. -/
theorem step_sound_local (s : Step n) (f : Fin n → Expr n) (hs : s.Valid f)
    (x : ℝ → Fin n → ℝ) (hx : Continuous x)
    (hd : ∀ t ∈ Icc (0:ℝ) s.duration, (∀ i, |x t i| ≤ (s.region:ℝ)) →
      HasDerivAt x (fun i => (f i).value (x t)) t)
    (hi : ‖x 0-curve s.coefficients 0‖ ≤ (s.initialError:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) s.duration, ‖x t-curve s.coefficients t‖ < (s.error:ℝ) := by
  obtain ⟨hT,hM,hL,hE,hB,hD,hclose,hcheck⟩ := hs
  have hTr : (0:ℝ) ≤ s.duration := by exact_mod_cast hT
  have hLr : (0:ℝ) ≤ s.lipschitz := by exact_mod_cast hL
  have hBr : (0:ℝ) < s.error := by exact_mod_cast hB
  have hDr : (0:ℝ) ≤ s.defect := by exact_mod_cast hD
  have hCr : (0:ℝ) ≤ (s.lipschitz:ℝ)*s.error+s.defect := by positivity
  have hclosed : (s.initialError:ℝ)+(s.duration:ℝ)*
      ((s.lipschitz:ℝ)*s.error+s.defect) < s.error := by exact_mod_cast hclose
  have hc : Continuous (curve s.coefficients) := continuous_iff_continuousAt.mpr
    (fun t => (curve_derivative s.coefficients t).continuousAt)
  apply IntegralTube.prefix_closure ((hx.sub hc).norm) (hi.trans_lt (by nlinarith))
  intro t ht hpref
  have hp (u : ℝ) (hu : u ∈ Icc 0 t) (i : Fin n) :
      |curve s.coefficients u i| ≤ (s.region:ℝ)-(s.error:ℝ) := by
    have hb := PolynomialBounds.bound_sound (s.coefficients i)
      (show |u| ≤ (s.duration:ℝ) by rw [abs_of_nonneg hu.1]; exact hu.2.trans ht.2)
    have hr : (PolynomialBounds.bound (s.coefficients i) s.duration:ℝ)+s.error ≤ s.region :=
      by exact_mod_cast (hcheck i).1
    change |curve s.coefficients u i| ≤ _ at hb
    linarith
  have he (u : ℝ) (hu : u ∈ Icc 0 t) (i : Fin n) :
      |x u i-curve s.coefficients u i| ≤ (s.error:ℝ) := by
    exact (show |x u i-curve s.coefficients u i| ≤ ‖x u-curve s.coefficients u‖ from
      by simpa [Real.norm_eq_abs] using norm_le_pi_norm (x u-curve s.coefficients u) i).trans (hpref u hu)
  have hxb (u : ℝ) (hu : u ∈ Icc 0 t) (i : Fin n) : |x u i| ≤ (s.region:ℝ) := by
    have h := abs_add_le (x u i-curve s.coefficients u i) (curve s.coefficients u i)
    simp only [sub_add_cancel] at h
    linarith [hp u hu i, he u hu i]
  have hdiff (u : ℝ) (hu : u ∈ Icc 0 t) :
      ‖(fun i => (f i).value (x u))-
        (fun i => evaluate ((differentiate (s.coefficients i)).map (Rat.castHom ℝ)) u)‖ ≤
      (s.lipschitz:ℝ)*s.error+s.defect := by
    apply (pi_norm_le_iff_of_nonneg hCr).mpr
    intro i
    have hlip := (f i).difference_bound hM (x u) (curve s.coefficients u) hBr.le
      (hxb u hu) (fun j => by linarith [hp u hu j]) (he u hu)
    have hres := residual_bound f s.coefficients
      (show |u| ≤ (s.duration:ℝ) by rw [abs_of_nonneg hu.1]; exact hu.2.trans ht.2) i
    have hδ : (PolynomialBounds.bound (residual f s.coefficients i) s.duration:ℝ) ≤ s.defect :=
      by exact_mod_cast (hcheck i).2.1
    have hSlope : ((f i).slope s.region:ℝ) ≤ s.lipschitz := by exact_mod_cast (hcheck i).2.2
    have hadd := abs_add_le ((f i).value (x u)-(f i).value (curve s.coefficients u))
      ((f i).value (curve s.coefficients u)-
        evaluate ((differentiate (s.coefficients i)).map (Rat.castHom ℝ)) u)
    simp only [sub_add_sub_cancel] at hadd
    rw [abs_sub_comm] at hres
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_right hSlope hBr.le]
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu => ((hd u ⟨hu.1, hu.2.trans ht.2⟩ (hxb u hu)).sub
      (curve_derivative s.coefficients u)).hasDerivWithinAt)
    (fun u hu => hdiff u (Ico_subset_Icc_self hu)) t (right_mem_Icc.mpr ht.1)
  simp only [sub_zero, Pi.sub_apply] at hm
  have hn := norm_sub_norm_le (x t-curve s.coefficients t) (x 0-curve s.coefficients 0)
  nlinarith [mul_le_mul_of_nonneg_left ht.2 hCr]

/-- Compose any valid per-step enclosure implication, using the existing
exact polynomial handoff theorem at every junction. -/
theorem chain_from_steps (S : ℕ → Step n) (f : Fin n → Expr n) (N : ℕ) {h : ℚ}
    (hh : 0 ≤ h) (hvalid : ∀ j < N, (S j).Valid f)
    (hduration : ∀ j < N, (S j).duration = h)
    (hjoin : ∀ j, j+1 < N → Compatible (S j) (S (j+1)))
    (x : ℝ → Fin n → ℝ)
    (hi : ‖x 0-curve (S 0).coefficients 0‖ ≤ ((S 0).initialError:ℝ))
    (hstep : ∀ j < N,
      ‖x ((j:ℝ)*h)-curve (S j).coefficients 0‖ ≤ ((S j).initialError:ℝ) →
      ∀ t ∈ Icc (0:ℝ) h, ‖x ((j:ℝ)*h+t)-curve (S j).coefficients t‖ < ((S j).error:ℝ)) :
    ∀ j < N, ∀ t ∈ Icc (0:ℝ) h,
      ‖x ((j:ℝ)*h+t)-curve (S j).coefficients t‖ < ((S j).error:ℝ) := by
  have hhr : (0:ℝ) ≤ h := by exact_mod_cast hh
  intro j
  induction j with
  | zero =>
    intro hj
    exact hstep 0 hj (by simpa using hi)
  | succ j ih =>
    intro hj
    have hj' : j < N := by omega
    have hprev := ih hj' (h:ℝ) ⟨hhr,le_rfl⟩
    have htime : (j:ℝ)*h+(h:ℝ) = ((j+1:ℕ):ℝ)*h := by push_cast; ring
    rw [htime] at hprev
    have hnext := handoff (S j) (S (j+1)) (hjoin j hj)
      (hvalid (j+1) hj).2.2.2.1 (x (((j+1:ℕ):ℝ)*h))
      (by simpa [hduration j hj'] using hprev.le)
    exact hstep (j+1) hj hnext

theorem chain_sound_local (S : ℕ → Step n) (f : Fin n → Expr n) (N : ℕ) {h R : ℚ}
    (hh : 0 ≤ h) (hvalid : ∀ j < N, (S j).Valid f)
    (hduration : ∀ j < N, (S j).duration = h)
    (hjoin : ∀ j, j+1 < N → Compatible (S j) (S (j+1)))
    (hregion : ∀ j < N, (S j).region ≤ R)
    (x : ℝ → Fin n → ℝ) (hx : Continuous x)
    (hd : ∀ t ∈ Icc (0:ℝ) ((N:ℝ)*h), (∀ i, |x t i| ≤ (R:ℝ)) →
      HasDerivAt x (fun i => (f i).value (x t)) t)
    (hi : ‖x 0-curve (S 0).coefficients 0‖ ≤ ((S 0).initialError:ℝ)) :
    ∀ j < N, ∀ t ∈ Icc (0:ℝ) h,
      ‖x ((j:ℝ)*h+t)-curve (S j).coefficients t‖ < ((S j).error:ℝ) := by
  have hhr : (0:ℝ) ≤ h := by exact_mod_cast hh
  apply chain_from_steps S f N hh hvalid hduration hjoin x hi
  intro j hj hinit t ht
  let shifted := fun u : ℝ => x ((j:ℝ)*h+u)
  have hshift : Continuous shifted := hx.comp (continuous_const.add continuous_id)
  have hder : ∀ u ∈ Icc (0:ℝ) (S j).duration,
      (∀ i, |shifted u i| ≤ ((S j).region:ℝ)) →
      HasDerivAt shifted (fun i => (f i).value (shifted u)) u := by
    intro u hu hb
    rw [hduration j hj] at hu
    have hjr : (j:ℝ)+1 ≤ N := by exact_mod_cast hj
    have hji : (0:ℝ) ≤ j := by positivity
    have hur : (j:ℝ)*h+u ∈ Icc (0:ℝ) ((N:ℝ)*h) :=
      ⟨add_nonneg (mul_nonneg hji hhr) hu.1,
        by nlinarith [mul_nonneg (sub_nonneg.mpr hjr) hhr, hu.2]⟩
    have hb' (i : Fin n) : |x ((j:ℝ)*h+u) i| ≤ (R:ℝ) :=
      (hb i).trans (by exact_mod_cast hregion j hj)
    simpa [shifted] using (hd _ hur hb').scomp u ((hasDerivAt_id u).const_add ((j:ℝ)*h))
  exact step_sound_local (S j) f (hvalid j hj) shifted hshift hder
    (by simpa [shifted] using hinit) t (by simpa [hduration j hj] using ht)

/-- Exact rational step certificates construct a solution of the original
polynomial ODE for the whole finite horizon. Existence is not an assumption.
The auxiliary clipped field is proved to agree along this solution. -/
theorem exists_solution_of_chain (S : ℕ → Step n) (f : Fin n → Expr n) (N : ℕ)
    {h R : ℚ} (hN : 0 < N) (hh : 0 ≤ h) (hR : 0 ≤ R)
    (hvalid : ∀ j < N, (S j).Valid f)
    (hduration : ∀ j < N, (S j).duration = h)
    (hjoin : ∀ j, j+1 < N → Compatible (S j) (S (j+1)))
    (hregion : ∀ j < N, (S j).region ≤ R)
    (K L : ℝ≥0) (hK : ∀ i, ((f i).slope R:ℝ) ≤ K)
    (hL : ∀ i, ((f i).majorant R:ℝ) ≤ L) (x₀ : Fin n → ℝ)
    (hi : ‖x₀-curve (S 0).coefficients 0‖ ≤ ((S 0).initialError:ℝ)) :
    ∃ x : ℝ → Fin n → ℝ, Continuous x ∧ x 0 = x₀ ∧
      ∀ t ∈ Icc (0:ℝ) ((N:ℝ)*h), HasDerivAt x (fun i => (f i).value (x t)) t := by
  have hhr : (0:ℝ) ≤ h := by exact_mod_cast hh
  obtain ⟨x,hx,hx₀,hdx⟩ := clippedField_exists f hR K L hK hL x₀
    (mul_nonneg (Nat.cast_nonneg N) hhr)
  have hd : ∀ t ∈ Icc (0:ℝ) ((N:ℝ)*h), (∀ i, |x t i| ≤ (R:ℝ)) →
      HasDerivAt x (fun i => (f i).value (x t)) t := by
    intro t ht hb
    simpa only [clippedField_eq f hb] using hdx t ht
  have he := chain_sound_local S f N hh hvalid hduration hjoin hregion x hx hd
    (by rw [hx₀]; exact hi)
  refine ⟨x,hx,hx₀,?_⟩
  intro t ht
  obtain ⟨j,hj,u,hu,htu⟩ := grid_covers N hhr hN ht
  apply hd t ht
  intro i
  rw [htu]
  exact (region_of_enclosure (S j) f (hvalid j hj)
    (by simpa [hduration j hj] using hu) (he j hj u hu) i).le.trans
      (by exact_mod_cast hregion j hj)

end GNC.PolynomialODE
