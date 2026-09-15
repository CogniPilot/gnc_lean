import GNC.Applications.OrbitalFuel.TerminalGravityTheory
import GNC.Applications.OrbitalFuel.TerminalResponse

/-! Identify the certified polynomial rows with the exact terminal gravity
integral. This is an algebraic and integral identity, before any error bound
or fuel-program reserve is applied.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.TerminalGravity
open GNC PolynomialOrbitTransition PolynomialBurn Matrix MeasureTheory Set

def normalizedOutput (z : Fin 5 → ℝ) (p : Fin 4 → ℝ) (n : Fin 2 → ℝ) (i : Fin 6) : ℝ :=
  ![z 0*z 4*p 0+z 1*z 4*p 1, -z 1*z 4*p 0+z 0*z 4*p 1, n 0,
    z 0*z 4*p 2+z 1*z 4*p 3, -z 1*z 4*p 2+z 0*z 4*p 3, n 1] i

def unitScale (speed : ℝ) (i : Fin 6) : ℝ :=
  (if i.val < 3 then (FreeResponse.lengthUnit:ℝ) else speed)/(FreeResponse.tolerance i:ℝ)

theorem output_scale (z : Fin 5 → ℝ) (p : Fin 4 → ℝ) (n : Fin 2 → ℝ)
    (speed : ℝ) (i : Fin 6) :
    TerminalResponse.output z speed p n i = unitScale speed i*normalizedOutput z p n i := by
  fin_cases i <;> simp [TerminalResponse.output, unitScale, normalizedOutput,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> ring

def outputMap (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 6) :
    ((Fin 4 → ℝ) × (Fin 2 → ℝ)) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun pn => normalizedOutput z (F *ᵥ pn.1) (H *ᵥ pn.2) i
    map_add' := fun a b => by
      simp only [Prod.fst_add, Prod.snd_add, mulVec_add]
      fin_cases i <;> simp [normalizedOutput, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> ring
    map_smul' := fun c a => by
      change normalizedOutput z (F *ᵥ (c • a.1)) (H *ᵥ (c • a.2)) i =
        c*normalizedOutput z (F *ᵥ a.1) (H *ᵥ a.2) i
      simp only [mulVec_smul]
      fin_cases i <;> simp [normalizedOutput, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> ring }

set_option maxHeartbeats 4000000 in
theorem kernel_pairing (x : Trajectory) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hx : x.state = fun t => pack (z t) (F t) (H t)) (i : Fin 6) (t : ℝ) (r : Vec3) :
    kernel x i t ⬝ᵥ r = normalizedOutput (z (3/5))
      (F (3/5) *ᵥ (planeInverse (F t) *ᵥ PlanarChaserError.planeInput r))
      (H (3/5) *ᵥ (normalInverse (H t) *ᵥ PlanarChaserError.normalInput r)) i := by
  fin_cases i <;>
    norm_num [kernel, input, hx, rowEntry, planeRow, frame, finalPlane, inversePlaneInput,
      sum4, PolynomialODE.Expr.value, pack, normalizedOutput, planeInverse, normalInverse,
      planeForm, normalForm, PlanarChaserError.planeInput, PlanarChaserError.normalInput,
      Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail]
  all_goals
    try simp only [show (⟨4,by decide⟩ : Fin 5) = 4 from rfl,
      show (⟨2,by decide⟩ : Fin 4) = 2 from rfl,
      show (⟨3,by decide⟩ : Fin 4) = 3 from rfl,
      show (Fin.succ (2:Fin 3)) = (3:Fin 4) from rfl]
    ring

theorem remainder_pairing (x : Trajectory) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hx : x.state = fun t => pack (z t) (F t) (H t))
    (hF : Continuous F) (hH : Continuous H) (r : ℝ → Vec3)
    (hr : ContinuousOn r (Icc (0:ℝ) (3/5))) (i : Fin 6) :
    normalizedOutput (z (3/5)) (ChaserResponse.planeRemainder F r)
      (ChaserResponse.normalRemainder H r) i =
      ∫ t in (0:ℝ)..(3/5), kernel x i t ⬝ᵥ r t := by
  let p := fun t => planeInverse (F t) *ᵥ PlanarChaserError.planeInput (r t)
  let n := fun t => normalInverse (H t) *ᵥ PlanarChaserError.normalInput (r t)
  have hrc (j : Fin 3) : ContinuousOn (fun t => r t j) (Icc (0:ℝ) (3/5)) :=
    (continuous_apply j).comp_continuousOn hr
  have hfc (j k : Fin 4) : ContinuousOn (fun t => F t j k) (Icc (0:ℝ) (3/5)) :=
    ((continuous_apply k).comp ((continuous_apply j).comp hF)).continuousOn
  have hhc (j k : Fin 2) : ContinuousOn (fun t => H t j k) (Icc (0:ℝ) (3/5)) :=
    ((continuous_apply k).comp ((continuous_apply j).comp hH)).continuousOn
  have hp : ContinuousOn p (Icc (0:ℝ) (3/5)) := by
    apply continuousOn_pi.mpr
    intro k
    fin_cases k <;>
      simp [p, planeInverse, planeForm, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply,
        dotProduct, Fin.sum_univ_succ, PlanarChaserError.planeInput,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.vecHead, Matrix.vecTail] <;> fun_prop
  have hn : ContinuousOn n (Icc (0:ℝ) (3/5)) := by
    apply continuousOn_pi.mpr
    intro k
    fin_cases k <;>
      simp [n, normalInverse, normalForm, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply,
        dotProduct, Fin.sum_univ_succ, PlanarChaserError.normalInput,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> fun_prop
  have hi := (hp.prodMk hn).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 3/5)
  have h := (outputMap (z (3/5)) (F (3/5)) (H (3/5)) i).intervalIntegral_comp_comm hi
  have hf := (ContinuousLinearMap.fst ℝ (Fin 4 → ℝ) (Fin 2 → ℝ)).intervalIntegral_comp_comm hi
  have hs := (ContinuousLinearMap.snd ℝ (Fin 4 → ℝ) (Fin 2 → ℝ)).intervalIntegral_comp_comm hi
  change (∫ t in (0:ℝ)..(3/5), p t) = (∫ t in (0:ℝ)..(3/5), (p t,n t)).1 at hf
  change (∫ t in (0:ℝ)..(3/5), n t) = (∫ t in (0:ℝ)..(3/5), (p t,n t)).2 at hs
  change (∫ t in (0:ℝ)..(3/5), normalizedOutput (z (3/5)) (F (3/5) *ᵥ p t) (H (3/5) *ᵥ n t) i) =
    normalizedOutput (z (3/5))
      (F (3/5) *ᵥ (∫ t in (0:ℝ)..(3/5), (p t,n t)).1)
      (H (3/5) *ᵥ (∫ t in (0:ℝ)..(3/5), (p t,n t)).2) i at h
  rw [← hf, ← hs] at h
  change normalizedOutput (z (3/5)) (F (3/5) *ᵥ (∫ t in (0:ℝ)..(3/5), p t))
    (H (3/5) *ᵥ (∫ t in (0:ℝ)..(3/5), n t)) i = _
  rw [← h]
  apply intervalIntegral.integral_congr
  intro t _
  exact (kernel_pairing x z F H hx i t (r t)).symm

end GNC.Applications.OrbitalFuel.TerminalGravity
