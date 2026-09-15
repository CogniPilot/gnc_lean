import GNC.Applications.OrbitalComparison.VaryingRateReference
import GNC.Dynamics.GravityQuadraticResponse

/-! Exact moving-frame reconstruction and full physical residual for a
varying-rate circular reference. Parameters are in the current time units;
normalizing physical time by T replaces μ by T² μ. The Euler term is retained.
No temporal or spatial Taylor series is assumed in these identities.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.OrbitalComparison.VaryingRateFrame
open SpatialBurn SpatialRotatingFrame Real
open scoped RealInnerProductSpace

theorem pack_components (x : E3) : pack (x 0) (x 1) (x 2)=x := by
  ext i
  fin_cases i <;> simp [pack_eq]

def turn (φ : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun x := mix φ (x 0) (x 1) (x 2)
  map_add' _ _ := mix_add _ _ _ _ _ _ _
  map_smul' _ _ := mix_smul _ _ _ _ _

def spin (w : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun x := pack (-w*x 1) (w*x 0) 0
  map_add' x y := by
    ext i
    fin_cases i <;> simp [pack_eq] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [pack_eq] <;> ring

theorem turn_norm (φ : ℝ) (x : E3) : ‖turn φ x‖=‖x‖ := by
  change ‖mix φ (x 0) (x 1) (x 2)‖=_
  rw [mix_norm,pack_components]

theorem turn_derivative {φ : ℝ → ℝ} {x : ℝ → E3} {w t : ℝ} {v : E3}
    (hφ : HasDerivAt φ w t) (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => turn (φ s) (x s)) (turn (φ t) (v+spin w (x t))) t := by
  have hi (i : Fin 3) : HasDerivAt (fun s => x s i) (v i) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hx
  convert mix_derivative hφ (hi 0) (hi 1) (hi 2) using 1
  simp [turn,spin,pack_eq,sub_eq_add_neg]

theorem spin_derivative {w : ℝ → ℝ} {x : ℝ → E3} {α t : ℝ} {v : E3}
    (hw : HasDerivAt w α t) (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => spin (w s) (x s)) (spin α (x t)+spin (w t) v) t := by
  have hi (i : Fin 3) : HasDerivAt (fun s => x s i) (v i) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hx
  have h := ((hw.neg.mul (hi 1)).smul_const e0).add ((hw.mul (hi 0)).smul_const e1)
  convert h using 1
  · funext s
    simp [spin,pack]
  · dsimp [spin,pack]
    module

def position (r : ℝ) (φ : ℝ → ℝ) (d : ℝ → E3) (t : ℝ) : E3 :=
  VaryingRateReference.position r (φ t)+turn (φ t) (d t)
def velocity (r : ℝ) (φ w : ℝ → ℝ) (d v : ℝ → E3) (t : ℝ) : E3 :=
  VaryingRateReference.velocity r (φ t) (w t)+turn (φ t) (v t+spin (w t) (d t))
def acceleration (r : ℝ) (φ w α : ℝ → ℝ) (d v a : ℝ → E3) (t : ℝ) : E3 :=
  VaryingRateReference.acceleration r (φ t) (w t) (α t)+
    turn (φ t) (a t+(2:ℝ) • spin (w t) (v t)+spin (α t) (d t)+spin (w t) (spin (w t) (d t)))

theorem position_derivative (r : ℝ) {φ w : ℝ → ℝ} {d v : ℝ → E3} {t : ℝ}
    (hφ : HasDerivAt φ (w t) t) (hd : HasDerivAt d (v t) t) :
    HasDerivAt (position r φ d) (velocity r φ w d v t) t :=
  (VaryingRateReference.position_derivative r hφ).add (turn_derivative hφ hd)

theorem velocity_derivative (r : ℝ) {φ w α : ℝ → ℝ} {d v a : ℝ → E3} {t : ℝ}
    (hφ : HasDerivAt φ (w t) t) (hw : HasDerivAt w (α t) t)
    (hd : HasDerivAt d (v t) t) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (velocity r φ w d v) (acceleration r φ w α d v a t) t := by
  have h := (VaryingRateReference.velocity_derivative r hφ hw).add
    (turn_derivative hφ (hv.add (spin_derivative hw hd)))
  convert h using 1
  simp only [acceleration,Pi.add_apply,map_add,map_smul]
  module

def gradient (k : ℝ) (x : E3) : E3 := pack (2*k*x 0) (-k*x 1) (-k*x 2)
def quadratic (k r : ℝ) (x : E3) : E3 :=
  (k/r) • pack (-3*x 0^2+(3/2)*(x 1^2+x 2^2)) (3*x 0*x 1) (3*x 0*x 2)
def positionOperator (k w α : ℝ) (x : E3) : E3 :=
  pack ((2*k+w^2)*x 0+α*x 1) ((-k+w^2)*x 1-α*x 0) (-k*x 2)
def velocityOperator (w : ℝ) (x : E3) : E3 := pack (2*w*x 1) (-2*w*x 0) 0

theorem reference_inner (r φ : ℝ) (x : E3) :
    ⟪VaryingRateReference.position r φ,turn φ x⟫=r*x 0 := by
  simp [VaryingRateReference.position,turn,mix,pack_eq,PiLp.inner_apply,Fin.sum_univ_succ]
  change (cos φ*x 0-sin φ*x 1)*(cos φ*r)+(sin φ*x 0+cos φ*x 1)*(sin φ*r)=_
  linear_combination r*x 0*(sin_sq_add_cos_sq φ)

theorem physical_gradient (μ r φ : ℝ) (hr : 0<r) (x : E3) :
    Gravity.gradient μ (VaryingRateReference.position r φ) (turn φ x)=
      turn φ (gradient (μ/r^3) x) := by
  rw [Gravity.gradient,VaryingRateReference.position_norm r φ hr.le,reference_inner]
  ext i
  fin_cases i <;>
    simp [turn,gradient,VaryingRateReference.position,mix,pack_eq] <;> field_simp <;> ring

theorem physical_quadratic (μ r φ : ℝ) (hr : 0<r) (x : E3) :
    (1/2:ℝ) • Gravity.hessian μ (VaryingRateReference.position r φ) (turn φ x) (turn φ x)=
      turn φ (quadratic (μ/r^3) r x) := by
  have hn := pack_norm_sq (x 0) (x 1) (x 2)
  rw [pack_components] at hn
  rw [Gravity.hessian,VaryingRateReference.position_norm r φ hr.le,reference_inner,
    real_inner_self_eq_norm_sq,turn_norm,hn]
  ext i
  fin_cases i <;>
    simp [turn,quadratic,VaryingRateReference.position,mix,pack_eq] <;> field_simp <;> ring

theorem operator_identity (k w α : ℝ) (d v a f : E3) :
    a+(2:ℝ) • spin w v+spin α d+spin w (spin w d)-gradient k d-f=
      a-positionOperator k w α d-velocityOperator w v-f := by
  ext i
  fin_cases i <;>
    simp [spin,gradient,positionOperator,velocityOperator,pack_eq] <;> ring

def residual (k r w α : ℝ) (d v a y f : E3) : E3 :=
  a-positionOperator k w α d-velocityOperator w v-f-quadratic k r y
def physicalAcceleration (μ r φ w α : ℝ) (δ p : E3) : E3 :=
  Gravity.field μ p+VaryingRateReference.thrust μ r φ w α+turn φ δ

theorem physical_defect_identity (μ r : ℝ) (hr : 0<r) (φ w α : ℝ → ℝ)
    (d v a y : ℝ → E3) (f δ : E3) (t : ℝ) :
    acceleration r φ w α d v a t-
      physicalAcceleration μ r (φ t) (w t) (α t) δ (position r φ d t)=
      turn (φ t) (residual (μ/r^3) r (w t) (α t) (d t) (v t) (a t) (y t) f)-
      Gravity.quadraticResidual μ (VaryingRateReference.position r (φ t))
        (turn (φ t) (d t)) (turn (φ t) (y t))+turn (φ t) (f-δ) := by
  rw [residual,map_sub,←physical_quadratic μ r (φ t) hr]
  rw [←operator_identity, map_sub,map_sub,←physical_gradient μ r (φ t) hr]
  rw [acceleration,←VaryingRateReference.physical_acceleration μ r (φ t) (w t) (α t) hr]
  dsimp [physicalAcceleration,position,Gravity.quadraticResidual]
  simp only [map_sub]
  module

/-- The same full-field budget applies to both parameter representations.
The radius gap is checked at the candidate; no actual-orbit tube is assumed. -/
theorem physical_defect_bound (μ r : ℝ) (hμ : 0≤μ) (hr : 0<r) (φ w α : ℝ → ℝ)
    (d v a y : ℝ → E3) (f δ : E3) (t : ℝ) {P Y E L S : ℝ}
    (hP : P<r) (hd : ‖d t‖≤P) (hy : ‖y t‖≤Y) (hdy : ‖d t-y t‖≤E)
    (hL : ‖residual (μ/r^3) r (w t) (α t) (d t) (v t) (a t) (y t) f‖≤L)
    (hS : ‖f-δ‖≤S) :
    ‖physicalAcceleration μ r (φ t) (w t) (α t) δ (position r φ d t)-
      acceleration r φ w α d v a t‖≤
      L+S+(3*μ/r^4)*E*(P+Y)+(4*μ/(r-P)^5)*P^3 := by
  have hg := Gravity.quadratic_residual_bound μ hμ
    (VaryingRateReference.position r (φ t)) (turn (φ t) (d t)) (turn (φ t) (y t))
    hP (by rw [VaryingRateReference.position_norm r (φ t) hr.le])
    (by simpa only [turn_norm] using hd) le_rfl (by simpa only [turn_norm] using hy)
    (by simpa only [←map_sub,turn_norm] using hdy)
  rw [norm_sub_rev,physical_defect_identity μ r hr φ w α d v a y f δ t]
  have hl : ‖turn (φ t) (residual (μ/r^3) r (w t) (α t) (d t) (v t) (a t) (y t) f)‖≤L :=
    by simpa only [turn_norm] using hL
  have hs : ‖turn (φ t) (f-δ)‖≤S := by simpa only [turn_norm] using hS
  have ht := (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add hl hg)) hs)
  convert ht using 1 <;> ring

end GNC.OrbitalComparison.VaryingRateFrame
