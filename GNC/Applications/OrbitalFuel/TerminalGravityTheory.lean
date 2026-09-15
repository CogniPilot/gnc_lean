import GNC.Applications.OrbitalFuel.TerminalGravityFormula
import GNC.Control.ThrustIntegral

/-! Continuous terminal transport bounds from the actual validated flow.
Terminal and intermediate entries are enclosed simultaneously; the norm is
the physical Euclidean norm, not the coordinatewise supremum norm.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.TerminalGravity
open GNC GNC.PolynomialODE GNC.PolynomialIntegral PolynomialTransition PolynomialBurn
open GNC.Planning.PolynomialKernel

def input (x : Trajectory) (t : ℝ) (i : Fin 50) : ℝ :=
  if h : i.val < 25 then x.state (3/5) ⟨i.val,h⟩
  else x.state t ⟨i.val-25,by omega⟩

def kernel (x : Trajectory) (i : Fin 6) (t : ℝ) : Vec3 :=
  fun k => (rowEntry i k).value (input x t)

theorem input_continuous (x : Trajectory) : Continuous (input x) := by
  apply continuous_pi
  intro i
  unfold input
  split_ifs
  · exact continuous_const
  · exact (continuous_apply _).comp x.continuous

theorem kernel_continuous (x : Trajectory) (i : Fin 6) : Continuous (kernel x i) :=
  continuous_pi (fun k => (rowEntry i k).value_continuous (input_continuous x))

theorem allowance_nonneg (j : Fin 32) (i : Fin 50) : 0 ≤ allowance j i := by
  unfold allowance
  split_ifs with h
  · unfold TerminalData.endpointError
    split_ifs <;> norm_num
  · exact ((steps_valid j).2 _).2.2.1.le

theorem region_nonneg (j : Fin 32) (i : Fin 50) : 0 ≤ region j i := by
  unfold region
  split_ifs with h
  · apply add_nonneg (abs_nonneg _)
    unfold TerminalData.endpointError
    split_ifs <;> norm_num
  · exact ((steps_valid j).2 _).1

theorem input_error (x : Trajectory) (j : Fin 32) {u : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) (3/160)) (i : Fin 50) :
    |input x ((j.val:ℝ)*(3/160)+u) i-curve (coefficients j) u i| ≤ (allowance j i:ℝ) := by
  by_cases h : i.val < 25
  · simpa [input, curve, coefficients, allowance, h, evaluate] using
      TerminalData.endpoint_enclosure x ⟨i.val,h⟩
  · simpa only [input, curve, coefficients, allowance, dif_neg h] using
      (x.cell_error j hu ⟨i.val-25,by omega⟩).le

theorem curve_region_allowance (j : Fin 32) {u : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) (3/160)) (i : Fin 50) :
    |curve (coefficients j) u i|+(allowance j i:ℝ) ≤ (region j i:ℝ) := by
  by_cases h : i.val < 25
  · simp [curve, coefficients, allowance, region, h, evaluate]
  · simp only [curve, coefficients, allowance, region, dif_neg h]
    have hb := PolynomialBounds.bound_sound ((steps j).coefficients ⟨i.val-25,by omega⟩)
      (show |u| ≤ ((steps j).duration:ℝ) by
        rw [durations, abs_of_nonneg hu.1]; norm_num; exact hu.2)
    have hr := ((steps_valid j).2 ⟨i.val-25,by omega⟩).2.2.2.2.2.1
    have hrR : (PolynomialBounds.bound ((steps j).coefficients ⟨i.val-25,by omega⟩)
          (steps j).duration:ℝ)+( (steps j).error ⟨i.val-25,by omega⟩:ℝ) ≤
        ((steps j).region ⟨i.val-25,by omega⟩:ℝ) := by exact_mod_cast hr
    linarith

theorem squared_enclosure (x : Trajectory) (j : Fin 32) {u : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) (3/160)) (i : Fin 6) :
    (squaredRow i).value (input x ((j.val:ℝ)*(3/160)+u)) ≤
      evaluate (((squaredRow i).coefficients (coefficients j)).map (Rat.castHom ℝ)) u+
        (squaredError:ℝ) := by
  have he := input_error x j hu
  have hr := curve_region_allowance j hu
  have hb (k) : (0:ℝ) ≤ (allowance j k:ℝ) := by exact_mod_cast allowance_nonneg j k
  have h := (squaredRow i).box_difference_bound (region_nonneg j) (allowance_nonneg j)
    (input x ((j.val:ℝ)*(3/160)+u)) (curve (coefficients j) u)
    (fun k => by
      have ha := abs_sub_le (input x ((j.val:ℝ)*(3/160)+u) k)
        (curve (coefficients j) u k) 0
      simp only [sub_zero] at ha
      linarith [he k, hr k])
    (fun k => by linarith [hr k, hb k]) he
  have hs : ((squaredRow i).differenceMajorant (region j) (allowance j):ℝ) ≤
      (squaredError:ℝ) := by exact_mod_cast squared_errors j i
  rw [Expr.coefficients_correct]
  change _ ≤ (squaredRow i).value (curve (coefficients j) u)+(squaredError:ℝ)
  linarith [(abs_le.mp h).2]

theorem kernel_squared (x : Trajectory) (i : Fin 6) (t : ℝ) :
    GNC.enorm (kernel x i t)^2 = (squaredRow i).value (input x t) := by
  rw [enorm_sq]
  simp only [lengthSq, kernel, squaredRow, Expr.value]
  ring

theorem cell_norm_bound (x : Trajectory) (j : Fin 32) (i : Fin 6) {ν : ℚ} (hν : 0 < ν) :
    (∫ t in ((j.val:ℝ)*(3/160))..((j.val:ℝ)*(3/160)+3/160), GNC.enorm (kernel x i t)) ≤
      (youngIntegral j i ν:ℝ) := by
  have h := PolynomialNormIntegral.rational_bound
    (fun u => ThrustSupport.euclideanEquiv (kernel x i ((j.val:ℝ)*(3/160)+u)))
    ((squaredRow i).coefficients (coefficients j))
    (a := 0) (b := 3/160) (ε := squaredError) (by norm_num)
    ((ThrustSupport.euclideanEquiv.continuous.comp ((kernel_continuous x i).comp
      (continuous_const.add continuous_id))).continuousOn) hν
    (fun u hu => by
      change GNC.enorm (kernel x i ((j.val:ℝ)*(3/160)+u))^2 ≤ _
      rw [kernel_squared]
      exact squared_enclosure x j (by norm_num at hu ⊢; exact hu) i)
  simp only [sub_zero] at h
  change (∫ u in ((0:ℚ):ℝ)..((3/160:ℚ):ℝ),
    GNC.enorm (kernel x i ((j.val:ℝ)*(3/160)+u))) ≤ (youngIntegral j i ν:ℝ) at h
  norm_num only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] at h
  rw [intervalIntegral.integral_comp_add_left (fun t => GNC.enorm (kernel x i t)), add_zero] at h
  exact h

end GNC.Applications.OrbitalFuel.TerminalGravity
