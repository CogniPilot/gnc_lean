import GNC.Applications.OrbitalFuel.TerminalData
import GNC.Applications.OrbitalFuel.BurnTheory

/-! Certified final reference/transition entries and exact SI square roots.
The final polynomial evaluation and its rounding are charged against the
already proved real-time ODE error.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.TerminalData
open GNC.PolynomialODE GNC.Planning.PolynomialKernel PolynomialTransition PolynomialBurn

def endpointError (i : Fin 25) : ℚ := if i.val < 5 then 1/10^19 else 1/10^16

set_option maxRecDepth 100000 in
theorem endpoint_budget : ∀ i, (steps 31).error i+1/10^25 ≤ endpointError i := by decide +kernel

theorem endpoint_enclosure (x : Trajectory) (i : Fin 25) :
    |x.state (3/5) i-(endpoint i:ℝ)| ≤ (endpointError i:ℝ) := by
  have h := x.cell_error 31 (u := 3/160) (by norm_num) i
  have ht : ((31:Fin 32).val:ℝ)*(3/160)+(3/160) = 3/5 := by norm_num
  rw [ht] at h
  have he := evaluate_map (Rat.castHom ℝ) ((steps 31).coefficients i) (3/160)
  change evaluate (((steps 31).coefficients i).map (Rat.castHom ℝ)) ((3/160:ℚ):ℝ) =
    ((evaluate ((steps 31).coefficients i) (3/160):ℚ):ℝ) at he
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at he
  change |x.state (3/5) i-evaluate (((steps 31).coefficients i).map (Rat.castHom ℝ)) (3/160)| < _ at h
  rw [he] at h
  have hr : |((evaluate ((steps 31).coefficients i) (3/160):ℚ):ℝ)-(endpoint i:ℝ)| ≤ (1/10^25:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (endpoint_rounding i)
    norm_num at h ⊢
    exact h
  have hb : ((steps 31).error i:ℝ)+(1/10^25:ℝ) ≤ (endpointError i:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (endpoint_budget i)
    norm_num at h ⊢
    exact h
  have ha := abs_sub_le (x.state (3/5) i)
    ((evaluate ((steps 31).coefficients i) (3/160):ℚ):ℝ) (endpoint i:ℝ)
  linarith

theorem speed_enclosure : |Real.sqrt (speedSquared:ℝ)-(speedCenter:ℝ)| ≤ (1/10^25:ℝ) := by
  obtain ⟨hl,hs,hu⟩ := speed_squared_bounds
  apply GNC.PolynomialEvaluation.sqrt_error (by norm_num [speedSquared]) (by norm_num)
  · have h := (Rat.cast_le (K := ℝ)).mpr hl
    norm_num at h ⊢
    exact h
  · have h := (Rat.cast_le (K := ℝ)).mpr hs
    norm_num at h ⊢
    exact h
  · have h := (Rat.cast_le (K := ℝ)).mpr hu
    norm_num at h ⊢
    exact h

theorem initialSpeed_enclosure : |Real.sqrt (3/2:ℝ)-(initialSpeedCenter:ℝ)| ≤ (1/10^25:ℝ) := by
  obtain ⟨hl,hs,hu⟩ := initialSpeed_squared_bounds
  apply GNC.PolynomialEvaluation.sqrt_error (by norm_num) (by norm_num)
  · have h := (Rat.cast_le (K := ℝ)).mpr hl
    norm_num at h ⊢
    exact h
  · have h := (Rat.cast_le (K := ℝ)).mpr hs
    norm_num at h ⊢
    exact h
  · have h := (Rat.cast_le (K := ℝ)).mpr hu
    norm_num at h ⊢
    exact h

end GNC.Applications.OrbitalFuel.TerminalData
