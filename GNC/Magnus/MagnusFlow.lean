import GNC.Magnus.MagnusAlgebra
import GNC.Analysis.FundamentalSolution

/-! Global continuous-input mixed factorization, without assuming that one
Magnus logarithm exists or converges over the entire interval. -/
noncomputable section
namespace GNC.Magnus
open NormedSpace
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exists_right_unit_flow (N : ℝ → A) (hN : Continuous N) :
    ∃ R : ℝ → Aˣ, R 0 = 1 ∧
      ∀ t, HasDerivAt (fun s => (R s : A)) ((R t : A)*N t) t := by
  obtain ⟨F,hF0,hF⟩ := LinearODE.exists_unit_solution (fun t => -N t) hN.neg
  refine ⟨fun t => (F t)⁻¹, by simp [hF0], ?_⟩
  intro t
  have hd := (hasFDerivAt_ringInverse (𝕜 := ℝ) (F t)).comp_hasDerivAt t (hF t)
  simp only [Function.comp_def, Ring.inverse_unit, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] at hd
  convert hd using 1
  simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
  rw [show (F t : A) * (↑(F t)⁻¹ : A) = 1 by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one], mul_one]

/-- Lemma 4 / Theorem 6 for all continuous left and right inputs. The
same two invertible factors work for every initial state. -/
theorem exists_mixed_flows (M N : ℝ → A) (hM : Continuous M) (hN : Continuous N) :
    ∃ L R : ℝ → Aˣ, L 0 = 1 ∧ R 0 = 1 ∧
      ∀ X₀ : A, (fun t => (L t : A)*X₀*(R t : A)) 0 = X₀ ∧
        ∀ t, HasDerivAt (fun s => (L s : A)*X₀*(R s : A))
          (M t*((L t : A)*X₀*(R t : A)) + ((L t : A)*X₀*(R t : A))*N t) t := by
  obtain ⟨L,hL0,hL⟩ := LinearODE.exists_unit_solution M hM
  obtain ⟨R,hR0,hR⟩ := exists_right_unit_flow N hN
  refine ⟨L,R,hL0,hR0,?_⟩
  intro X₀
  exact ⟨by simp [hL0,hR0], fun t => factor_derivative (hL t) (hR t)⟩

theorem mixed_flow_unique (M N : ℝ → A) (hM : Continuous M) (hN : Continuous N)
    (X Y : ℝ → A) (hX : ∀ t, HasDerivAt X (M t*X t+X t*N t) t)
    (hY : ∀ t, HasDerivAt Y (M t*Y t+Y t*N t) t) (h0 : X 0 = Y 0) : X = Y := by
  let C : ℝ → A →L[ℝ] A := fun t =>
    ContinuousLinearMap.mul ℝ A (M t) + (ContinuousLinearMap.mul ℝ A).flip (N t)
  have hC : Continuous C :=
    ((ContinuousLinearMap.mul ℝ A).continuous.comp hM).add
      ((ContinuousLinearMap.mul ℝ A).flip.continuous.comp hN)
  funext t
  exact LinearODE.unique_continuous C hC (fun s _ => hX s) (fun s _ => hY s)
    (a := -(|t|+1)) (b := |t|+1) (t₀ := 0)
    ⟨by linarith [abs_nonneg t],by positivity⟩ h0
    (abs_lt.mp (by linarith : |t| < |t|+1))

end GNC.Magnus
