import GNC.Applications.OrbitalFuel.BurnSchedule
import GNC.Analysis.PrefixResponse

/-! All-time prefixes of the solar burn/coast schedule. Truncating a burn
at the query time gives its exact partial integral; future burns vanish.
No sampled time grid or differentiability at a switching instant is used.
-/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Elementwise
namespace GNC.Applications.OrbitalFuel.BurnPrefix
open GNC.SymplecticResponse BurnSchedule

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem burn_integrals {n m : Type*} [Fintype n] [Fintype m]
    (K : ℝ → Matrix n m ℝ) (u : Fin 18 → ℝ → m → ℝ) (t : ℝ) :
    (∑ k ∈ Finset.range 37,
      ∫ s in min (time k:ℝ) t..min (time (k+1):ℝ) t, K s *ᵥ input u k s) =
      ∑ j : Fin 18,
        ∫ s in min (PolynomialBurn.burnStart j:ℝ) t..min (PolynomialBurn.burnFinish j:ℝ) t,
          K s *ᵥ u j s := by
  norm_num [Finset.sum_range_succ, Fin.sum_univ_succ, input, time,
    PolynomialBurn.burnStart, PolynomialBurn.burnFinish]
  abel

theorem endpoint {n : Type*} [Fintype n] [DecidableEq n]
    (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ) (x : ℝ → n → ℝ)
    (u : Fin 18 → ℝ → n → ℝ) (v : ℝ → n → ℝ)
    (hJ : J*J = -1) (hF : Continuous F) (hx : Continuous x)
    (hu : ∀ j, Continuous (u j)) (hv : ContinuousOn v (Set.Icc (0:ℝ) (3/5)))
    (hdF : ∀ s ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (A s*F s) s)
    (hA : ∀ s ∈ Set.Icc (0:ℝ) (3/5), (A s)ᵀ*J+J*A s = 0)
    (hiF : F 0 = 1)
    (hdx : ∀ k < 37, ∀ s ∈ Set.Ioo (time k:ℝ) (time (k+1):ℝ),
      HasDerivAt x (A s *ᵥ x s+(input u k s+v s)) s)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (3/5)) :
    x t = F t *ᵥ (x 0+
      (∑ j : Fin 18,
        ∫ s in min (PolynomialBurn.burnStart j:ℝ) t..min (PolynomialBurn.burnFinish j:ℝ) t,
          pullback J (F s) *ᵥ u j s)+
      ∫ s in (0:ℝ)..t, pullback J (F s) *ᵥ v s) := by
  let K := fun s => pullback J (F s)
  have hK : Continuous K :=
    (continuous_const.matrix_mul hF.matrix_transpose).matrix_mul continuous_const
  have hmul : Continuous (fun z : Matrix n n ℝ × (n → ℝ) => z.1 *ᵥ z.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hvc := hmul.comp_continuousOn (hK.continuousOn.prodMk hv)
  have hiu (k : ℕ) (_hk : k < 37) : IntervalIntegrable
      (fun s => K s *ᵥ input u k s) MeasureTheory.volume (time k:ℝ) (time (k+1):ℝ) :=
    (hK.matrix_mulVec (input_continuous hu k)).intervalIntegrable _ _
  have hiv (k : ℕ) (hk : k < 37) : IntervalIntegrable
      (fun s => K s *ᵥ v s) MeasureTheory.volume (time k:ℝ) (time (k+1):ℝ) :=
    (hvc.mono (Set.Icc_subset_Icc (horizon k hk).1 (horizon k hk).2)).intervalIntegrable_of_Icc
      (order k hk)
  have h := piecewise_prefix F A J x (fun k s => input u k s+v s)
    (fun k => (time k:ℝ)) 37 ht hJ hF hx hdF hA hiF
    (by norm_num [time_zero]) (by norm_num [time_final]) order horizon hdx
    (fun k hk => by simpa only [mulVec_add] using (hiu k hk).add (hiv k hk))
  rw [piecewise_integral_add F J (input u) v (fun k => min (time k:ℝ) t) 37
    (fun k hk => clipped_integrable (order k hk) (hiu k hk) t)
    (fun k hk => clipped_integrable (order k hk) (hiv k hk) t), burn_integrals] at h
  norm_num only [time_zero, time_final, Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] at h
  rw [min_eq_left ht.1, min_eq_right ht.2] at h
  simpa only [add_assoc] using h

end GNC.Applications.OrbitalFuel.BurnPrefix
