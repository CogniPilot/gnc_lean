import GNC.Applications.OrbitalFuel.BurnFormula
import GNC.Analysis.PiecewiseResponse

/-! The actual solar schedule: eighteen finite burns separated by nineteen
coasts. All thirty-seven arcs partition the normalized horizon [0, 3/5].
The input for an arc is an extension, used only on that open interval.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.BurnSchedule
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

def time (k : ℕ) : ℚ :=
  if k = 0 then 0 else if k = 37 then 3/5
  else if k%2 = 1 then ((k/2:ℕ):ℚ)/30+1/150
  else ((k/2-1:ℕ):ℚ)/30+2/75

theorem time_zero : time 0 = 0 := by norm_num [time]
theorem time_final : time 37 = 3/5 := by norm_num [time]

theorem time_certificate : ∀ k : Fin 37,
    0 ≤ time k.val ∧ time k.val ≤ time (k.val+1) ∧ time (k.val+1) ≤ 3/5 := by
  decide +kernel

theorem burn_start (j : Fin 18) : time (2*j.val+1) = PolynomialBurn.burnStart j := by
  fin_cases j <;> norm_num [time, PolynomialBurn.burnStart]

theorem burn_finish (j : Fin 18) : time (2*j.val+2) = PolynomialBurn.burnFinish j := by
  fin_cases j <;> norm_num [time, PolynomialBurn.burnFinish]

def input {E : Type*} [Zero E] (u : Fin 18 → ℝ → E) (k : ℕ) (t : ℝ) : E :=
  if hk : k < 37 ∧ k%2 = 1 then u ⟨k/2,by omega⟩ t else 0

theorem input_burn {E : Type*} [Zero E] (u : Fin 18 → ℝ → E) (j : Fin 18) (t : ℝ) :
    input u (2*j.val+1) t = u j t := by
  simp [input, show 2*j.val+1 < 37 by omega]
  congr 1
  apply Fin.ext
  dsimp
  omega

theorem input_coast {E : Type*} [Zero E] (u : Fin 18 → ℝ → E) (j : Fin 19) (t : ℝ) :
    input u (2*j.val) t = 0 := by simp [input]

theorem input_continuous {E : Type*} [TopologicalSpace E] [Zero E]
    {u : Fin 18 → ℝ → E} (hu : ∀ j, Continuous (u j)) (k : ℕ) :
    Continuous (input u k) := by
  change Continuous (fun t => input u k t)
  by_cases hk : k < 37 ∧ k%2 = 1
  · simpa [input, hk] using hu ⟨k/2,by omega⟩
  · simpa [input, hk] using (continuous_const : Continuous (fun _ : ℝ => (0:E)))

theorem order (k : ℕ) (hk : k < 37) : (time k:ℝ) ≤ (time (k+1):ℝ) := by
  exact_mod_cast (time_certificate ⟨k,hk⟩).2.1

theorem horizon (k : ℕ) (hk : k < 37) : 0 ≤ (time k:ℝ) ∧ (time (k+1):ℝ) ≤ 3/5 := by
  constructor
  · exact_mod_cast (time_certificate ⟨k,hk⟩).1
  · have h := (Rat.cast_le (K := ℝ)).mpr (time_certificate ⟨k,hk⟩).2.2
    norm_num at h ⊢
    exact h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Removing the zero coast integrals leaves precisely the eighteen
finite-burn integrals used by the certified coefficient matrix. -/
theorem burn_integrals {n m : Type*} [Fintype n] [Fintype m]
    (K : ℝ → Matrix n m ℝ) (u : Fin 18 → ℝ → m → ℝ) :
    (∑ k ∈ Finset.range 37, ∫ t in (time k:ℝ)..(time (k+1):ℝ), K t *ᵥ input u k t) =
      ∑ j : Fin 18, ∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
        K t *ᵥ u j t := by
  norm_num [Finset.sum_range_succ, Fin.sum_univ_succ, input, time,
    PolynomialBurn.burnStart, PolynomialBurn.burnFinish]
  abel

/-- Exact response for the eighteen rectangular burns and a continuous
common forcing. The trajectory ODE is imposed only inside each arc. -/
theorem endpoint {n : Type*} [Fintype n] [DecidableEq n]
    (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ) (x : ℝ → n → ℝ)
    (u : Fin 18 → ℝ → n → ℝ) (v : ℝ → n → ℝ)
    (hJ : J*J = -1) (hF : Continuous F) (hx : Continuous x)
    (hu : ∀ j, Continuous (u j)) (hv : ContinuousOn v (Set.Icc (0:ℝ) (3/5)))
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (A t*F t) t)
    (hA : ∀ t ∈ Set.Icc (0:ℝ) (3/5), (A t)ᵀ*J+J*A t = 0)
    (hiF : F 0 = 1)
    (hdx : ∀ k < 37, ∀ t ∈ Set.Ioo (time k:ℝ) (time (k+1):ℝ),
      HasDerivAt x (A t *ᵥ x t+(input u k t+v t)) t) :
    x (3/5) = F (3/5) *ᵥ (x 0+
      (∑ j : Fin 18, ∫ t in (PolynomialBurn.burnStart j:ℝ)..(PolynomialBurn.burnFinish j:ℝ),
        GNC.SymplecticResponse.pullback J (F t) *ᵥ u j t)+
      ∫ t in (0:ℝ)..(3/5), GNC.SymplecticResponse.pullback J (F t) *ᵥ v t) := by
  let K := fun t => GNC.SymplecticResponse.pullback J (F t)
  have hK : Continuous K :=
    (continuous_const.matrix_mul hF.matrix_transpose).matrix_mul continuous_const
  have hmul : Continuous (fun z : Matrix n n ℝ × (n → ℝ) => z.1 *ᵥ z.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hvc := hmul.comp_continuousOn (hK.continuousOn.prodMk hv)
  have hiu (k : ℕ) (_hk : k < 37) : IntervalIntegrable
      (fun t => K t *ᵥ input u k t) MeasureTheory.volume (time k:ℝ) (time (k+1):ℝ) :=
    (hK.matrix_mulVec (input_continuous hu k)).intervalIntegrable _ _
  have hiv (k : ℕ) (hk : k < 37) : IntervalIntegrable
      (fun t => K t *ᵥ v t) MeasureTheory.volume (time k:ℝ) (time (k+1):ℝ) :=
    (hvc.mono (Set.Icc_subset_Icc (horizon k hk).1 (horizon k hk).2)).intervalIntegrable_of_Icc
      (order k hk)
  have h := GNC.SymplecticResponse.piecewise_endpoint F A J x
    (fun k t => input u k t+v t) (fun k => (time k:ℝ)) 37 (by norm_num) hJ hF hx hdF hA hiF
    (by norm_num [time_zero]) (by norm_num [time_final]) order horizon hdx
    (fun k hk => by simpa only [mulVec_add] using (hiu k hk).add (hiv k hk))
  rw [GNC.SymplecticResponse.piecewise_integral_add F J (input u) v
    (fun k => (time k:ℝ)) 37 hiu hiv, burn_integrals] at h
  norm_num only [time_zero, time_final, Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] at h
  simpa only [add_assoc] using h

end GNC.Applications.OrbitalFuel.BurnSchedule
