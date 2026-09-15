import GNC.Applications.OrbitalFuel.RetainedPrefixPhysics
import GNC.Applications.OrbitalFuel.RetainedPrefixForward

/-! Combining the one common pointing direction commutes with finite sums,
integration, and the forward transition. This is an exact linear identity.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPrefix
open GNC Matrix
set_option autoImplicit false

def combination (q : Vec3) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) 0+
    q 0 • ContinuousLinearMap.proj (R := ℝ) 1+
    q 1 • ContinuousLinearMap.proj (R := ℝ) 2+
    q 2 • ContinuousLinearMap.proj (R := ℝ) 3

theorem combination_apply (q : Vec3) (a : Fin 4 → ℝ) : combination q a = combine a q := by
  simp [combination,combine]

theorem combine_add (a b : Fin 4 → ℝ) (q : Vec3) :
    combine (a+b) q = combine a q+combine b q := by
  simp only [← combination_apply,map_add]

theorem combine_sum {ι : Type*} [Fintype ι] (a : ι → Fin 4 → ℝ) (q : Vec3) :
    combine (∑ j, a j) q = ∑ j, combine (a j) q := by
  simp only [← combination_apply,map_sum]

theorem combine_integral (f : ℝ → Fin 4 → ℝ) (hf : Continuous f) (q : Vec3) (a b : ℝ) :
    combine (fun k => ∫ t in a..b, f t k) q = ∫ t in a..b, combine (f t) q := by
  have hint := hf.intervalIntegrable (μ := MeasureTheory.volume) a b
  have he : (fun k => ∫ t in a..b, f t k) = ∫ t in a..b, f t := by
    ext k
    exact (ContinuousLinearMap.proj (R := ℝ) k).intervalIntegral_comp_comm hint
  rw [he]
  simpa only [combination_apply] using ((combination q).intervalIntegral_comp_comm hint).symm

theorem combine_forward (A : Matrix (Fin 6) (Fin 6) ℝ) (c : Fin 6 → Fin 4 → ℝ)
    (q : Vec3) (i : Fin 6) :
    combine (fun k => (A *ᵥ (fun r => c r k)) i) q =
      (A *ᵥ (fun r => combine (c r) q)) i := by
  have he : (fun r => combine (c r) q) =
      (fun r => c r 0)+q 0 • (fun r => c r 1)+
        q 1 • (fun r => c r 2)+q 2 • (fun r => c r 3) := rfl
  rw [he]
  simp only [combine,mulVec_add,mulVec_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]

def planeRows (y : Fin 6 → ℝ) : Fin 4 → ℝ := ![y 0,y 1,y 2,y 3]
def normalRows (y : Fin 6 → ℝ) : Fin 2 → ℝ := ![y 4,y 5]
def cartesian (p : Fin 4 → ℝ) (n : Fin 2 → ℝ) : Fin 6 → ℝ := ![p 0,p 1,n 0,p 2,p 3,n 1]

theorem matrixValue_packed (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (y : Fin 6 → ℝ) :
    matrixValue (PolynomialOrbitTransition.pack z F H) *ᵥ y =
      cartesian (F *ᵥ planeRows y) (H *ᵥ normalRows y) := by
  ext i
  fin_cases i <;>
    simp [matrixValue,cartesian,planeRows,normalRows,PolynomialOrbitTransition.pack_plane,
      PolynomialOrbitTransition.pack_normal,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail]

end GNC.Applications.OrbitalFuel.RetainedPrefix
