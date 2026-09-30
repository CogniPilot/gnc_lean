import GNC.Dynamics.KeplerAnomaly
import GNC.Dynamics.RotatingGravityClosedForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Explicit Yamanaka–Ankersen fundamental columns in radial/transverse
coordinates, with primes in true anomaly. Columns are reordered and rescaled
relative to the conventional along-track, negative-normal, negative-radial presentation.
The secular primitive satisfies J'=1/(1+e cos f)^2. All formulas below are
checked by differentiation, including the secular column and nonsingularity. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Matrix Real
open scoped Matrix.Norms.Operator
namespace GNC.YamanakaAnkersen
open ClassicalOrbitEquivalence KeplerAnomaly
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

def planeGenerator (k : ℝ) : M4 :=
  !![0,0,1,0; 0,0,0,1; 3/k,0,0,2; 0,0,-2,0]

def plane (e f : ℝ) (j : ℝ → ℝ) : M4 :=
  !![(((1:ℝ) + (e * (Real.cos f))) * (Real.sin f)), ((Real.cos f) * ((1:ℝ) + (e * (Real.cos f)))), ((2:ℝ) + (e * (-3:ℝ) * ((1:ℝ) + (e * (Real.cos f))) * (j f) * (Real.sin f))), (0:ℝ);
     ((Real.cos f) * ((2:ℝ) + (e * (Real.cos f)))), (((-2:ℝ) + (e * (-1:ℝ) * (Real.cos f))) * (Real.sin f)), (((-3:ℝ) + (e * (-3:ℝ) * (Real.cos f))) * ((1:ℝ) + (e * (Real.cos f))) * (j f)), (1:ℝ);
     ((Real.cos f) + (e * (((Real.cos f) ^ 2) + ((-1:ℝ) * ((Real.sin f) ^ 2))))), (((-1:ℝ) * (Real.sin f)) + (e * (-2:ℝ) * (Real.cos f) * (Real.sin f))), (e * (-3:ℝ) * ((((Real.cos f) + (e * (((Real.cos f) ^ 2) + ((-1:ℝ) * ((Real.sin f) ^ 2))))) * (j f)) + ((((1:ℝ) + (e * (Real.cos f))))⁻¹ * (Real.sin f)))), (0:ℝ);
     (((-2:ℝ) + (e * (-2:ℝ) * (Real.cos f))) * (Real.sin f)), (e + ((-1:ℝ) * ((2:ℝ) + (e * (2:ℝ) * (Real.cos f))) * (Real.cos f))), ((-3:ℝ) + (e * (6:ℝ) * ((1:ℝ) + (e * (Real.cos f))) * (j f) * (Real.sin f))), (0:ℝ)]

theorem plane_derivative {e f : ℝ} {j : ℝ → ℝ}
    (hk : kappa e f ≠ 0)
    (hj : HasDerivAt j (1/(kappa e f)^2) f) :
    HasDerivAt (fun x => plane e x j)
      (planeGenerator (kappa e f) * plane e f j) f := by
  dsimp [kappa] at hk hj
  have hc := sin_sq_add_cos_sq f
  have h00 : HasDerivAt (fun x => (((1:ℝ) + (e * (Real.cos x))) * (Real.sin x)))
      ((Real.cos f) + (e * (((Real.cos f) ^ 2) + ((-1:ℝ) * ((Real.sin f) ^ 2))))) f := by
    convert (((hasDerivAt_const f (1:ℝ)).add ((hasDerivAt_const f e).mul (hasDerivAt_cos f))).mul (hasDerivAt_sin f)) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h01 : HasDerivAt (fun x => ((Real.cos x) * ((1:ℝ) + (e * (Real.cos x)))))
      (((-1:ℝ) * (Real.sin f)) + (e * (-2:ℝ) * (Real.cos f) * (Real.sin f))) f := by
    convert ((hasDerivAt_cos f).mul ((hasDerivAt_const f (1:ℝ)).add ((hasDerivAt_const f e).mul (hasDerivAt_cos f)))) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h02 : HasDerivAt (fun x => ((2:ℝ) + (e * (-3:ℝ) * ((1:ℝ) + (e * (Real.cos x))) * (j x) * (Real.sin x))))
      (e * (-3:ℝ) * ((((Real.cos f) + (e * (((Real.cos f) ^ 2) + ((-1:ℝ) * ((Real.sin f) ^ 2))))) * (j f)) + ((((1:ℝ) + (e * (Real.cos f))))⁻¹ * (Real.sin f)))) f := by
    convert ((hasDerivAt_const f (2:ℝ)).add (((((hasDerivAt_const f e).mul (hasDerivAt_const f (-3:ℝ))).mul ((hasDerivAt_const f (1:ℝ)).add ((hasDerivAt_const f e).mul (hasDerivAt_cos f)))).mul hj).mul (hasDerivAt_sin f))) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h03 : HasDerivAt (fun x => (0:ℝ))
      (0:ℝ) f := by
    convert (hasDerivAt_const f (0:ℝ)) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h10 : HasDerivAt (fun x => ((Real.cos x) * ((2:ℝ) + (e * (Real.cos x)))))
      (((-2:ℝ) + (e * (-2:ℝ) * (Real.cos f))) * (Real.sin f)) f := by
    convert ((hasDerivAt_cos f).mul ((hasDerivAt_const f (2:ℝ)).add ((hasDerivAt_const f e).mul (hasDerivAt_cos f)))) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h11 : HasDerivAt (fun x => (((-2:ℝ) + (e * (-1:ℝ) * (Real.cos x))) * (Real.sin x)))
      (e + ((-1:ℝ) * ((2:ℝ) + (e * (2:ℝ) * (Real.cos f))) * (Real.cos f))) f := by
    convert (((hasDerivAt_const f (-2:ℝ)).add (((hasDerivAt_const f e).mul (hasDerivAt_const f (-1:ℝ))).mul (hasDerivAt_cos f))).mul (hasDerivAt_sin f)) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h12 : HasDerivAt (fun x => (((-3:ℝ) + (e * (-3:ℝ) * (Real.cos x))) * ((1:ℝ) + (e * (Real.cos x))) * (j x)))
      ((-3:ℝ) + (e * (6:ℝ) * ((1:ℝ) + (e * (Real.cos f))) * (j f) * (Real.sin f))) f := by
    convert ((((hasDerivAt_const f (-3:ℝ)).add (((hasDerivAt_const f e).mul (hasDerivAt_const f (-3:ℝ))).mul (hasDerivAt_cos f))).mul ((hasDerivAt_const f (1:ℝ)).add ((hasDerivAt_const f e).mul (hasDerivAt_cos f)))).mul hj) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h13 : HasDerivAt (fun x => (1:ℝ))
      (0:ℝ) f := by
    convert (hasDerivAt_const f (1:ℝ)) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h20 : HasDerivAt (fun x => ((Real.cos x) + (e * (((Real.cos x) ^ 2) + ((-1:ℝ) * ((Real.sin x) ^ 2))))))
      (((3:ℝ) * (Real.sin f)) + (((-2:ℝ) + (e * (-2:ℝ) * (Real.cos f))) * (2:ℝ) * (Real.sin f))) f := by
    convert ((hasDerivAt_cos f).add ((hasDerivAt_const f e).mul (((hasDerivAt_cos f).pow 2).add ((hasDerivAt_const f (-1:ℝ)).mul ((hasDerivAt_sin f).pow 2))))) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h21 : HasDerivAt (fun x => (((-1:ℝ) * (Real.sin x)) + (e * (-2:ℝ) * (Real.cos x) * (Real.sin x))))
      ((e * (2:ℝ)) + ((3:ℝ) * (Real.cos f)) + ((-2:ℝ) * ((2:ℝ) + (e * (2:ℝ) * (Real.cos f))) * (Real.cos f))) f := by
    convert (((hasDerivAt_const f (-1:ℝ)).mul (hasDerivAt_sin f)).add ((((hasDerivAt_const f e).mul (hasDerivAt_const f (-2:ℝ))).mul (hasDerivAt_cos f)).mul (hasDerivAt_sin f))) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h22 : HasDerivAt (fun x => (e * (-3:ℝ) * ((((Real.cos x) + (e * (((Real.cos x) ^ 2) + ((-1:ℝ) * ((Real.sin x) ^ 2))))) * (j x)) + ((((1:ℝ) + (e * (Real.cos x))))⁻¹ * (Real.sin x)))))
      ((-6:ℝ) + (((2:ℝ) + (e * (-3:ℝ) * ((1:ℝ) + (e * (Real.cos f))) * (j f) * (Real.sin f))) * (((1:ℝ) + (e * (Real.cos f))))⁻¹ * (3:ℝ)) + (e * (12:ℝ) * ((1:ℝ) + (e * (Real.cos f))) * (j f) * (Real.sin f))) f := by
    convert (((hasDerivAt_const f e).mul (hasDerivAt_const f (-3:ℝ))).mul ((((hasDerivAt_cos f).add ((hasDerivAt_const f e).mul (((hasDerivAt_cos f).pow 2).add ((hasDerivAt_const f (-1:ℝ)).mul ((hasDerivAt_sin f).pow 2))))).mul hj).add ((((hasDerivAt_const f (1:ℝ)).add ((hasDerivAt_const f e).mul (hasDerivAt_cos f))).inv hk).mul (hasDerivAt_sin f)))) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h23 : HasDerivAt (fun x => (0:ℝ))
      (0:ℝ) f := by
    convert (hasDerivAt_const f (0:ℝ)) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h30 : HasDerivAt (fun x => (((-2:ℝ) + (e * (-2:ℝ) * (Real.cos x))) * (Real.sin x)))
      (((-2:ℝ) * (Real.cos f)) + (e * (-2:ℝ) * (((Real.cos f) ^ 2) + ((-1:ℝ) * ((Real.sin f) ^ 2))))) f := by
    convert (((hasDerivAt_const f (-2:ℝ)).add (((hasDerivAt_const f e).mul (hasDerivAt_const f (-2:ℝ))).mul (hasDerivAt_cos f))).mul (hasDerivAt_sin f)) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h31 : HasDerivAt (fun x => (e + ((-1:ℝ) * ((2:ℝ) + (e * (2:ℝ) * (Real.cos x))) * (Real.cos x))))
      (((2:ℝ) * (Real.sin f)) + (e * (4:ℝ) * (Real.cos f) * (Real.sin f))) f := by
    convert ((hasDerivAt_const f e).add (((hasDerivAt_const f (-1:ℝ)).mul ((hasDerivAt_const f (2:ℝ)).add (((hasDerivAt_const f e).mul (hasDerivAt_const f (2:ℝ))).mul (hasDerivAt_cos f)))).mul (hasDerivAt_cos f))) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h32 : HasDerivAt (fun x => ((-3:ℝ) + (e * (6:ℝ) * ((1:ℝ) + (e * (Real.cos x))) * (j x) * (Real.sin x))))
      (e * (6:ℝ) * ((((Real.cos f) + (e * (((Real.cos f) ^ 2) + ((-1:ℝ) * ((Real.sin f) ^ 2))))) * (j f)) + ((((1:ℝ) + (e * (Real.cos f))))⁻¹ * (Real.sin f)))) f := by
    convert ((hasDerivAt_const f (-3:ℝ)).add (((((hasDerivAt_const f e).mul (hasDerivAt_const f (6:ℝ))).mul ((hasDerivAt_const f (1:ℝ)).add ((hasDerivAt_const f e).mul (hasDerivAt_cos f)))).mul hj).mul (hasDerivAt_sin f))) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  have h33 : HasDerivAt (fun x => (0:ℝ))
      (0:ℝ) f := by
    convert (hasDerivAt_const f (0:ℝ)) using 1 <;>
      dsimp <;> field_simp [hk] <;> first | (solve | ring) | (solve | linear_combination e*hc) | (solve | linear_combination -e*hc) | (solve | linear_combination 2*e*hc) | (solve | linear_combination -2*e*hc) | (solve | linear_combination 2*e*(1+e*cos f)*hc) | (solve | linear_combination -2*e*(1+e*cos f)*hc)
  apply hasDerivAt_pi.mpr; intro r
  apply hasDerivAt_pi.mpr; intro c
  fin_cases r <;> fin_cases c
  · convert h00 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h01 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h02 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h03 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h10 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h11 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h12 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h13 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h20 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h21 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h22 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h23 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h30 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h31 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h32 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring
  · convert h33 using 1 <;> simp [plane, planeGenerator, kappa, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one] <;> field_simp [hk] <;> ring

theorem plane_det {e f : ℝ} (hk : kappa e f ≠ 0) (j : ℝ → ℝ) :
    (plane e f j).det = e^2-1 := by
  dsimp [kappa] at hk
  let F := plane e f j
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    !![F 0 0,F 0 1,F 0 2; F 2 0,F 2 1,F 2 2; F 3 0,F 3 1,F 3 2]
  have hm : F.submatrix (1 : Fin 4).succAbove (3 : Fin 4).succAbove = M := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h0 : F 0 3 = 0 := rfl
  have h1 : F 1 3 = 1 := rfl
  have h2 : F 2 3 = 0 := rfl
  have h3 : F 3 3 = 0 := rfl
  have h3' : F (Fin.succ 2) 3 = 0 := rfl
  have hd : F.det = (F.submatrix (1 : Fin 4).succAbove (3 : Fin 4).succAbove).det := by
    rw [Matrix.det_succ_column _ 3]
    norm_num [Fin.sum_univ_succ, h0, h1, h2, h3, h3']
  change F.det = _
  rw [hd, hm, Matrix.det_fin_three]
  change (((1:ℝ) + (e * (Real.cos f))) * (Real.sin f)) * (((-1:ℝ) * (Real.sin f)) + (e * (-2:ℝ) * (Real.cos f) * (Real.sin f))) * ((-3:ℝ) + (e * (6:ℝ) * ((1:ℝ) + (e * (Real.cos f))) * (j f) * (Real.sin f)))
    - (((1:ℝ) + (e * (Real.cos f))) * (Real.sin f)) * (e * (-3:ℝ) * ((((Real.cos f) + (e * (((Real.cos f) ^ 2) + ((-1:ℝ) * ((Real.sin f) ^ 2))))) * (j f)) + ((((1:ℝ) + (e * (Real.cos f))))⁻¹ * (Real.sin f)))) * (e + ((-1:ℝ) * ((2:ℝ) + (e * (2:ℝ) * (Real.cos f))) * (Real.cos f)))
    - ((Real.cos f) * ((1:ℝ) + (e * (Real.cos f)))) * ((Real.cos f) + (e * (((Real.cos f) ^ 2) + ((-1:ℝ) * ((Real.sin f) ^ 2))))) * ((-3:ℝ) + (e * (6:ℝ) * ((1:ℝ) + (e * (Real.cos f))) * (j f) * (Real.sin f)))
    + ((Real.cos f) * ((1:ℝ) + (e * (Real.cos f)))) * (e * (-3:ℝ) * ((((Real.cos f) + (e * (((Real.cos f) ^ 2) + ((-1:ℝ) * ((Real.sin f) ^ 2))))) * (j f)) + ((((1:ℝ) + (e * (Real.cos f))))⁻¹ * (Real.sin f)))) * (((-2:ℝ) + (e * (-2:ℝ) * (Real.cos f))) * (Real.sin f))
    + ((2:ℝ) + (e * (-3:ℝ) * ((1:ℝ) + (e * (Real.cos f))) * (j f) * (Real.sin f))) * ((Real.cos f) + (e * (((Real.cos f) ^ 2) + ((-1:ℝ) * ((Real.sin f) ^ 2))))) * (e + ((-1:ℝ) * ((2:ℝ) + (e * (2:ℝ) * (Real.cos f))) * (Real.cos f)))
    - ((2:ℝ) + (e * (-3:ℝ) * ((1:ℝ) + (e * (Real.cos f))) * (j f) * (Real.sin f))) * (((-1:ℝ) * (Real.sin f)) + (e * (-2:ℝ) * (Real.cos f) * (Real.sin f))) * (((-2:ℝ) + (e * (-2:ℝ) * (Real.cos f))) * (Real.sin f)) = e^2-1
  field_simp [hk]
  linear_combination (-(cos f)^2*e^2-2*cos f*e+e^2-1)*
    (sin_sq_add_cos_sq f)

def normal (f : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos f,sin f; -sin f,cos f]

def normalGenerator : Matrix (Fin 2) (Fin 2) ℝ := !![0,1; -1,0]

theorem normal_derivative (f : ℝ) :
    HasDerivAt normal (normalGenerator * normal f) f := by
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  fin_cases i <;> fin_cases j
  · simpa [normalGenerator, normal, Matrix.mul_apply, Fin.sum_univ_succ] using hasDerivAt_cos f
  · simpa [normalGenerator, normal, Matrix.mul_apply, Fin.sum_univ_succ] using hasDerivAt_sin f
  · simpa [normalGenerator, normal, Matrix.mul_apply, Fin.sum_univ_succ] using (hasDerivAt_sin f).neg
  · simpa [normalGenerator, normal, Matrix.mul_apply, Fin.sum_univ_succ] using hasDerivAt_cos f

theorem normal_det (f : ℝ) : (normal f).det = 1 := by
  simpa [normal, Matrix.det_fin_two, pow_two] using cos_sq_add_sin_sq f

abbrev Block6 := Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) ℝ
def basis (e : ℝ) (j : ℝ → ℝ) (f : ℝ) : Block6 := fromBlocks (plane e f j) 0 0 (normal f)
def generator (k : ℝ) : Block6 := fromBlocks (planeGenerator k) 0 0 normalGenerator

theorem basis_derivative {e f : ℝ} {j : ℝ → ℝ} (hk : kappa e f ≠ 0)
    (hj : HasDerivAt j (1/(kappa e f)^2) f) :
    HasDerivAt (basis e j) (generator (kappa e f) * basis e j f) f := by
  convert NilpotentInteraction.blocks_derivative (plane_derivative hk hj)
    (hasDerivAt_const f (0 : Matrix (Fin 4) (Fin 2) ℝ)) (normal_derivative f) using 1
  simp [basis, generator, fromBlocks_multiply]

theorem basis_det {e f : ℝ} (hk : kappa e f ≠ 0) (j : ℝ → ℝ) :
    (basis e j f).det = e^2-1 := by
  rw [basis, Matrix.det_fromBlocks_zero₂₁, plane_det hk, normal_det, mul_one]

theorem basis_nonsingular {e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (j : ℝ → ℝ) (f : ℝ) : IsUnit (basis e j f).det := by
  rw [basis_det (kappa_pos he he1 f).ne']
  apply isUnit_iff_ne_zero.mpr
  have hpos : 0 < (1-e)*(1+e) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- In this block ordering the canonical TH generator is literally the
YA planar block plus the independent harmonic normal block. -/
theorem th_reindex (k : ℝ) :
    (th k).submatrix RotatingGravity.originalIndex RotatingGravity.originalIndex =
      generator k := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [th, generator, planeGenerator, normalGenerator, RotatingGravity.originalIndex,
      Matrix.submatrix, RadialGravityFrame.omega, skew, Matrix.cons_val_two]

def secular (e f₀ f : ℝ) : ℝ := ∫ s in f₀..f, 1/(kappa e s)^2

theorem secular_derivative {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) (f₀ f : ℝ) :
    HasDerivAt (secular e f₀) (1/(kappa e f)^2) f := by
  have hc : Continuous (fun s => (1:ℝ)/(kappa e s)^2) :=
    continuous_const.div
      ((continuous_const.add (continuous_const.mul continuous_cos)).pow 2)
      (fun s => pow_ne_zero 2 (kappa_pos he he1 s).ne')
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable f₀ f)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

def transition (e : ℝ) (j : ℝ → ℝ) (f₀ f : ℝ) : Block6 :=
  basis e j f * (basis e j f₀)⁻¹

theorem transition_initial {e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (j : ℝ → ℝ) (f₀ : ℝ) : transition e j f₀ f₀ = 1 :=
  Matrix.mul_nonsing_inv _ (basis_nonsingular he he1 j f₀)

/-- The explicit YA formula solves TH, not merely an assumed fundamental
matrix. The secular primitive and its nonsingularity are proved above. -/
theorem transition_derivative {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) (f₀ f : ℝ) :
    HasDerivAt (transition e (secular e f₀) f₀)
      (generator (kappa e f) * transition e (secular e f₀) f₀ f) f := by
  unfold transition
  simpa only [mul_assoc] using (basis_derivative (kappa_pos he he1 f).ne'
    (secular_derivative he he1 f₀ f)).mul_const ((basis e (secular e f₀) f₀)⁻¹)

/-- Along the physical Kepler clock, the apparent quadrature is just
h/p² times elapsed time. No numerical quadrature is needed for YA. -/
theorem secular_along_kepler {e h p : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (f : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (rate e h p (f t)) t) (t₀ t : ℝ) :
    secular e (f t₀) (f t) = h/p^2*(t-t₀) := by
  have hd (s : ℝ) : HasDerivAt
      (fun u => secular e (f t₀) (f u)-h/p^2*(u-t₀)) 0 s := by
    have hk := (kappa_pos he he1 (f s)).ne'
    convert ((secular_derivative he he1 (f t₀) (f s)).comp s (hf s)).sub
      (((hasDerivAt_id s).sub_const t₀).const_mul (h/p^2)) using 1
    simp [rate, smul_eq_mul]
    field_simp <;> ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t t₀
  apply sub_eq_zero.mp
  simpa [secular] using hc

theorem time_transition_derivative {e h p : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    {f : ℝ → ℝ} {t : ℝ}
    (hf : HasDerivAt f (rate e h p (f t)) t) (t₀ : ℝ) :
    HasDerivAt (fun s => transition e (secular e (f t₀)) (f t₀) (f s))
      ((rate e h p (f t) • generator (kappa e (f t))) *
        transition e (secular e (f t₀)) (f t₀) (f t)) t := by
  simpa only [smul_mul_assoc] using (transition_derivative he he1 (f t₀) (f t)).scomp t hf

end GNC.YamanakaAnkersen
