import GNC.Applications.OrbitalComparison.SpatialBurn

/-! Exact three-dimensional reconstruction from the prescribed rotating frame.
The normal component is retained. These identities do not truncate the
nonlinear gravity response or assert termination of a Magnus series.
-/
noncomputable section
namespace GNC.OrbitalComparison.SpatialRotatingFrame
open SpatialBurn Real

def mix (φ x y z : ℝ) : E3 :=
  pack (cos φ*x-sin φ*y) (sin φ*x+cos φ*y) z

theorem mix_add (φ x y z a b c : ℝ) :
    mix φ (x+a) (y+b) (z+c) = mix φ x y z+mix φ a b c := by
  dsimp [mix,pack]
  module

theorem mix_sub (φ x y z a b c : ℝ) :
    mix φ (x-a) (y-b) (z-c) = mix φ x y z-mix φ a b c := by
  dsimp [mix,pack]
  module

theorem mix_smul (φ r x y z : ℝ) :
    mix φ (r*x) (r*y) (r*z) = r • mix φ x y z := by
  dsimp [mix,pack]
  module

theorem mix_norm_sq (φ x y z : ℝ) :
    ‖mix φ x y z‖^2 = x^2+y^2+z^2 := by
  rw [mix,pack_norm_sq]
  calc
    _ = (sin φ^2+cos φ^2)*(x^2+y^2)+z^2 := by ring
    _ = _ := by rw [sin_sq_add_cos_sq]; ring

theorem mix_norm (φ x y z : ℝ) : ‖mix φ x y z‖ = ‖pack x y z‖ := by
  have h := mix_norm_sq φ x y z
  rw [← pack_norm_sq] at h
  nlinarith [norm_nonneg (mix φ x y z),norm_nonneg (pack x y z)]

@[simp] theorem mix_zero (x y z : ℝ) : mix 0 x y z = pack x y z := by
  simp [mix]

/-- The moving frame contributes its angular-velocity term exactly. -/
theorem mix_derivative {φ x y z : ℝ → ℝ} {w dx dy dz t : ℝ}
    (hφ : HasDerivAt φ w t) (hx : HasDerivAt x dx t)
    (hy : HasDerivAt y dy t) (hz : HasDerivAt z dz t) :
    HasDerivAt (fun s => mix (φ s) (x s) (y s) (z s))
      (mix (φ t) (dx-w*y t) (dy+w*x t) dz) t := by
  have h := ((((hφ.cos.mul hx).sub (hφ.sin.mul hy)).smul_const e0).add
    (((hφ.sin.mul hx).add (hφ.cos.mul hy)).smul_const e1)).add (hz.smul_const e2)
  convert h using 1
  dsimp [mix,pack]
  module

theorem rtn_source (θ t : ℝ) :
    SpatialBurn.source .rtnReferenceOffset θ t =
      mix ((UniformCertificate.omega:ℝ)*t) (cos θ) ((4/5)*sin θ) ((3/5)*sin θ) := by
  rw [SpatialBurn.source_components]
  dsimp [SpatialBurn.components,mix]
  congr 1 <;> ring

end GNC.OrbitalComparison.SpatialRotatingFrame
