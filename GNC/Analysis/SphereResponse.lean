import GNC.Lie.SpatialPointing
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! A quadratic response to an arbitrary unit thrust direction uses eight
nonconstant direction functions. The sphere relation removes one response
column without choosing an uncertainty rotation axis. This is a span identity,
not a minimal-dimension or numerical-complexity theorem. -/
noncomputable section
namespace GNC.SphereResponse
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def quadratic (u v c : ℝ) (U V C Uu Uv Vv Cu Cv Cc : E) : E :=
  u • U+v • V+c • C+u^2 • Uu+(u*v) • Uv+v^2 • Vv+
    (c*u) • Cu+(c*v) • Cv+c^2 • Cc

def reduced (u v c : ℝ) (U V C Uu Uv Vv Cu Cv : E) : E :=
  u • U+v • V+c • C+u^2 • Uu+(u*v) • Uv+v^2 • Vv+
    (c*u) • Cu+(c*v) • Cv

theorem reduction (u v c : ℝ) (hs : u^2+v^2=2*c-c^2)
    (U V C Uu Uv Vv Cu Cv Cc : E) :
    quadratic u v c U V C Uu Uv Vv Cu Cv Cc =
      reduced u v c U V (C+2 • Cc) (Uu-Cc) Uv (Vv-Cc) Cu Cv := by
  have hc : c^2=2*c-u^2-v^2 := by linarith
  unfold quadratic reduced
  rw [hc]
  module

/-- The coefficients may be arbitrary response vectors at any fixed time.
Both pointing coordinates vary independently; no planar-motion hypothesis
or small-angle approximation is used. -/
theorem angular_reduction (a b : ℝ) (U V C Uu Uv Vv Cu Cv Cc : E) :
    quadratic (Real.sin a*Real.cos b) (Real.sin b) (1-Real.cos a*Real.cos b)
      U V C Uu Uv Vv Cu Cv Cc =
    reduced (Real.sin a*Real.cos b) (Real.sin b) (1-Real.cos a*Real.cos b)
      U V (C+2 • Cc) (Uu-Cc) Uv (Vv-Cc) Cu Cv :=
  reduction _ _ _ (SpatialPointing.sphere_relation a b) _ _ _ _ _ _ _ _ _

/-- Every actual SO(3) attitude supplies the same reduction, without an
Euler-angle chart. Roll about the prescribed thrust axis has no effect on
this instantaneous direction; subsequent direction histories still matter. -/
theorem rotation_reduction (R : SO3) (U V C Uu Uv Vv Cu Cv Cc : E) :
    let n := rotate R ![1,0,0]
    quadratic (n 1) (n 2) (1-n 0) U V C Uu Uv Vv Cu Cv Cc =
    reduced (n 1) (n 2) (1-n 0) U V (C+2 • Cc) (Uu-Cc) Uv (Vv-Cc) Cu Cv := by
  dsimp only
  have h : lengthSq (rotate R ![1,0,0]) = 1 := by
    rw [rotate_lengthSq]
    change (1:ℝ)^2+0^2+0^2=1
    norm_num
  unfold lengthSq at h
  apply reduction
  nlinarith

/-- A forward-pointing cap has a rational axial-depth bound. The parameter
`h` bounds squared transverse displacement, not an angle or a tolerance. -/
theorem cap_depth_bound {u v c h : ℝ} (hc0 : 0≤c) (hc1 : c≤1)
    (hh : h<1) (hs : u^2+v^2=2*c-c^2) (huv : u^2+v^2≤h) :
    c ≤ h/(2-h) := by
  have hcc : c^2≤c := by nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  have hch : c≤h := by linarith
  apply (le_div_iff₀ (by linarith : 0<2-h)).2
  nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hch)]

/-- Expanding a symmetric Hessian applied to the first response supplies
the nine unreduced linear/quadratic columns. -/
theorem bilinear_expansion (B : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hs : ∀ x y, B x y=B y x) (u v c : ℝ) (U V C : E) :
    B (u • U+v • V+c • C) (u • U+v • V+c • C) =
      u^2 • B U U+(u*v) • (2 • B U V)+v^2 • B V V+
      (c*u) • (2 • B C U)+(c*v) • (2 • B C V)+c^2 • B C C := by
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply]
  rw [hs V U,hs U C,hs V C]
  module

theorem quadratic_bilinear_reduction (B : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hB : ∀ x y, B x y=B y x) (u v c : ℝ) (hs : u^2+v^2=2*c-c^2)
    (U V C : E) :
    u • U+v • V+c • C+(1/2:ℝ) • B (u • U+v • V+c • C) (u • U+v • V+c • C) =
      reduced u v c U V (C+B C C) ((1/2:ℝ) • (B U U-B C C))
        (B U V) ((1/2:ℝ) • (B V V-B C C)) (B C U) (B C V) := by
  calc
    _ = quadratic u v c U V C ((1/2:ℝ) • B U U) (B U V)
          ((1/2:ℝ) • B V V) (B C U) (B C V) ((1/2:ℝ) • B C C) := by
      rw [bilinear_expansion B hB]
      unfold quadratic
      module
    _ = _ := by
      rw [reduction u v c hs]
      unfold reduced
      module

def basis (u v c : ℝ) : Fin 8 → ℝ := ![u,v,c,u^2,u*v,v^2,c*u,c*v]

section Dynamics
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def response (P : Fin 8 → ℝ → F) (u v c t : ℝ) : F :=
  ∑ i, basis u v c i • P i t

theorem response_derivative (A : ℝ → F →L[ℝ] F) (P f : Fin 8 → ℝ → F)
    (u v c t : ℝ) (h : ∀ i, HasDerivAt (P i) (A t (P i t)+f i t) t) :
    HasDerivAt (response P u v c)
      (A t (response P u v c t)+response f u v c t) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (h i).const_smul (basis u v c i))
  simpa only [response,map_sum,map_smul,smul_add,Finset.sum_add_distrib] using hd

theorem response_initial (P : Fin 8 → ℝ → F) (u v c : ℝ)
    (h : ∀ i, P i 0=0) : response P u v c 0=0 := by
  simp [response,h]

end Dynamics

end GNC.SphereResponse
