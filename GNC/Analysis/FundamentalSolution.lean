import GNC.Analysis.LinearODE
import GNC.Analysis.ForcedResponse
import Mathlib.Analysis.Normed.Operator.Mul

/-! Construction of an invertible fundamental solution for every continuous
coefficient, and the resulting unconditional variation-of-constants theorem. -/
noncomputable section
open Set
namespace GNC.LinearODE

theorem exists_unit_solution {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
    (A : ℝ → B) (hA : Continuous A) :
    ∃ Φ : ℝ → Bˣ, Φ 0 = 1 ∧ ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t := by
  let L := fun t => ContinuousLinearMap.mul ℝ B (A t)
  let R := fun t => -(ContinuousLinearMap.mul ℝ B).flip (A t)
  have hL : Continuous L := (ContinuousLinearMap.mul ℝ B).continuous.comp hA
  have hR : Continuous R := ((ContinuousLinearMap.mul ℝ B).flip.continuous.comp hA).neg
  obtain ⟨F,hF₀,hF⟩ := exists_solution L hL (1:B)
  obtain ⟨G,hG₀,hG⟩ := exists_solution R hR (1:B)
  have hdF (t : ℝ) : HasDerivAt F (A t*F t) t := hF t
  have hdG (t : ℝ) : HasDerivAt G (-G t*A t) t := by
    simpa [R, ContinuousLinearMap.mul_apply] using hG t
  have hGF (t : ℝ) : G t*F t = 1 := by
    have hd (s : ℝ) : HasDerivAt (fun z => G z*F z) 0 s := by
      convert (hdG s).mul (hdF s) using 1
      noncomm_ring
    have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa [hF₀,hG₀] using h
  let C := fun t => L t+R t
  have hC : Continuous C := hL.add hR
  have hdFG (s : ℝ) : HasDerivAt (fun z => F z*G z) (C s (F s*G s)) s := by
    convert (hdF s).mul (hdG s) using 1
    simp [C,L,R,ContinuousLinearMap.mul_apply,mul_assoc]
  have hdOne (s : ℝ) : HasDerivAt (fun _ : ℝ => (1:B)) (C s 1) s := by
    simpa [C,L,R,ContinuousLinearMap.mul_apply] using hasDerivAt_const s (1:B)
  have hFG (t : ℝ) : F t*G t = 1 := by
    exact unique_continuous C hC (fun s _ => hdFG s) (fun s _ => hdOne s)
      (a := -(|t|+1)) (b := |t|+1) (t₀ := 0)
      ⟨by linarith [abs_nonneg t],by positivity⟩ (by simp [hF₀,hG₀])
      (abs_lt.mp (by linarith : |t| < |t|+1))
  let Φ := fun t => (⟨F t,G t,hFG t,hGF t⟩ : Bˣ)
  exact ⟨Φ,Units.ext hF₀,hdF⟩

end GNC.LinearODE

namespace GNC.ForcedResponse
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The previously explicit fundamental-solution hypothesis is satisfied
by every continuous operator coefficient. -/
theorem exists_fundamental (A : ℝ → End (V := V)) (hA : Continuous A) :
    ∃ Φ : ℝ → (End (V := V))ˣ, Φ 0 = 1 ∧
      ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t :=
  LinearODE.exists_unit_solution A hA

def fundamental (A : ℝ → End (V := V)) (hA : Continuous A) : ℝ → (End (V := V))ˣ :=
  (exists_fundamental A hA).choose

theorem fundamental_initial (A : ℝ → End (V := V)) (hA : Continuous A) :
    fundamental A hA 0 = 1 := (exists_fundamental A hA).choose_spec.1

theorem fundamental_derivative (A : ℝ → End (V := V)) (hA : Continuous A) (t : ℝ) :
    HasDerivAt (fun s => (fundamental A hA s).val) (A t*(fundamental A hA t).val) t :=
  (exists_fundamental A hA).choose_spec.2 t

/-- Equations (77)–(78), including existence: the actual integral built
from the constructed fundamental solution is the unique ODE solution. -/
theorem exists_unique_response (A : ℝ → End (V := V)) (hA : Continuous A)
    (u : ℝ → V) (hu : Continuous u) (x₀ : V) :
    ∃! f : ℝ → V, f 0 = x₀ ∧ ∀ t, HasDerivAt f (A t (f t)+u t) t := by
  let Φ := fundamental A hA
  have hΦ := fundamental_derivative A hA
  have h₀ := fundamental_initial A hA
  refine ⟨response Φ u x₀,⟨response_initial Φ h₀ u x₀,response_derivative Φ A hΦ u hu x₀⟩,?_⟩
  intro f hf
  have heq := response_unique Φ A hΦ h₀ u hu f hf.2
  simpa only [hf.1] using heq

end GNC.ForcedResponse
