import GNC.Applications.OrbitalComparison.VaryingRateForcing
import GNC.Applications.OrbitalComparison.VaryingRateFrame
import GNC.Dynamics.ScaledForcedOrbitExistence
import GNC.Dynamics.PolynomialOrbitCertificate

/-! A full inverse-square orbit with a changing-speed powered circular
reference and a fixed oblique inertial attitude offset. Time is normalized
to [0,1]; μ is the physical gravity parameter multiplied by duration squared.
The coarse existence region is distinct from the prediction-error bound.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.OrbitalComparison.VaryingRateBurn
open SpatialBurn Set
open scoped Matrix

structure Model where
  μ : ℝ
  r : ℝ
  w0 : ℝ
  slope : ℝ

def Model.phase (m : Model) (t : ℝ) : ℝ := m.w0*t+m.slope*t^2/2
def Model.rate (m : Model) (t : ℝ) : ℝ := m.w0+m.slope*t
def Model.radial (m : Model) (t : ℝ) : ℝ := m.r*(m.μ/m.r^3-(m.rate t)^2)
def Model.tangent (m : Model) : ℝ := m.r*m.slope
def Model.reference (m : Model) (t : ℝ) : E3 := VaryingRateReference.position m.r (m.phase t)
def Model.referenceVelocity (m : Model) (t : ℝ) : E3 :=
  VaryingRateReference.velocity m.r (m.phase t) (m.rate t)
def Model.nominalThrust (m : Model) (t : ℝ) : E3 :=
  VaryingRateReference.thrust m.μ m.r (m.phase t) (m.rate t) m.slope
def Model.source (m : Model) (θ t : ℝ) : E3 :=
  VaryingRateForcing.source θ (m.phase t) (m.radial t) m.tangent
def Model.relativeThrust (m : Model) (θ t : ℝ) : E3 :=
  VaryingRateFrame.turn (m.phase t) (m.source θ t)
def Model.thrust (m : Model) (θ t : ℝ) : E3 := m.nominalThrust t+m.relativeThrust θ t
def Model.acceleration (m : Model) (θ t : ℝ) (p : E3) : E3 := Gravity.field m.μ p+m.thrust θ t

theorem Model.acceleration_frame (m : Model) (θ t : ℝ) (p : E3) :
    m.acceleration θ t p=VaryingRateFrame.physicalAcceleration m.μ m.r (m.phase t) (m.rate t)
      m.slope (m.source θ t) p := by
  dsimp [Model.acceleration,Model.thrust,Model.nominalThrust,Model.relativeThrust,
    VaryingRateFrame.physicalAcceleration]
  module

theorem Model.phase_derivative (m : Model) (t : ℝ) : HasDerivAt m.phase (m.rate t) t := by
  convert ((hasDerivAt_id t).const_mul m.w0).add
    (((hasDerivAt_id t).pow 2).const_mul m.slope |>.div_const 2) using 1
  dsimp [Model.rate]
  ring

theorem Model.rate_derivative (m : Model) (t : ℝ) : HasDerivAt m.rate m.slope t := by
  change HasDerivAt (fun s => m.w0+m.slope*s) m.slope t
  convert (hasDerivAt_const t m.w0).add ((hasDerivAt_id t).const_mul m.slope) using 1
  simp

theorem Model.reference_derivative (m : Model) (t : ℝ) :
    HasDerivAt m.reference (m.referenceVelocity t) t :=
  VaryingRateReference.position_derivative _ (m.phase_derivative t)

theorem Model.referenceVelocity_derivative (m : Model) (hr : 0<m.r) (t : ℝ) :
    HasDerivAt m.referenceVelocity (Gravity.field m.μ (m.reference t)+m.nominalThrust t) t :=
  VaryingRateReference.physical_velocity_derivative _ _ hr
    (m.phase_derivative t) (m.rate_derivative t)

theorem Model.reference_norm (m : Model) (hr : 0≤m.r) (t : ℝ) : ‖m.reference t‖=m.r :=
  VaryingRateReference.position_norm _ _ hr

theorem Model.reference_continuous (m : Model) : Continuous m.reference :=
  continuous_iff_continuousAt.mpr fun t => (m.reference_derivative t).continuousAt
theorem Model.referenceVelocity_continuous (m : Model) (hr : 0<m.r) : Continuous m.referenceVelocity :=
  continuous_iff_continuousAt.mpr fun t => (m.referenceVelocity_derivative hr t).continuousAt

theorem Model.relativeThrust_continuous (m : Model) (θ : ℝ) : Continuous (m.relativeThrust θ) := by
  unfold Model.relativeThrust Model.source VaryingRateForcing.source
    VaryingRateForcing.first VaryingRateForcing.second
  simp only [VaryingRateForcing.phase_re,VaryingRateForcing.phase_im]
  dsimp [VaryingRateFrame.turn,SpatialRotatingFrame.mix,VaryingRateForcing.s0,
    VaryingRateForcing.sCos,VaryingRateForcing.sSin,VaryingRateForcing.c0,
    VaryingRateForcing.cCos1,VaryingRateForcing.cSin1,VaryingRateForcing.cCos2,
    VaryingRateForcing.cSin2,pack,Model.radial,Model.tangent,Model.phase,Model.rate]
  fun_prop

theorem Model.relativeThrust_bound (m : Model) (θ t : ℝ) {σ L : ℝ}
    (hθ : |θ|≤σ) (hL : |m.radial t|+|m.tangent|≤L) :
    ‖m.relativeThrust θ t‖≤((7/5)*σ+(83/100)*σ^2)*L := by
  rw [Model.relativeThrust,VaryingRateFrame.turn_norm]
  exact VaryingRateForcing.source_norm θ (m.phase t) (m.radial t) m.tangent hθ hL

theorem turn_matrix (φ : ℝ) (v : Vec3) :
    (VaryingRateFrame.turn φ (WithLp.toLp 2 v)).ofLp=AxisRotation.zMatrix φ *ᵥ v := by
  ext i
  fin_cases i <;> simp [VaryingRateFrame.turn,SpatialRotatingFrame.mix,pack_eq,
    AxisRotation.zMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem nominalThrust_components (m : Model) (hr : 0<m.r) (t : ℝ) :
    m.nominalThrust t=VaryingRateFrame.turn (m.phase t) (pack (m.radial t) m.tangent 0) := by
  have hradius : m.μ/m.r^2-m.r*(m.rate t)^2=m.radial t := by
    dsimp [Model.radial]
    field_simp [hr.ne']
    <;> ring
  ext i
  fin_cases i <;> simp [Model.nominalThrust,VaryingRateReference.thrust,VaryingRateFrame.turn,
    SpatialRotatingFrame.mix,pack_eq,←hradius,Model.tangent]

/-- The source is exactly a fixed inertial attitude offset acting on the
nominal command. This ties the harmonic representation to physical rotation. -/
theorem Model.thrust_physical (m : Model) (hr : 0<m.r) (θ t : ℝ) :
    (m.thrust θ t).ofLp=(attitude θ).val *ᵥ (m.nominalThrust t).ofLp := by
  have hneg (φ : ℝ) : AxisRotation.zMatrix (-φ)=(AxisRotation.zMatrix φ).transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [AxisRotation.zMatrix,Matrix.transpose_apply]
  have hunit (φ : ℝ) : AxisRotation.zMatrix φ*AxisRotation.zMatrix (-φ)=1 := by
    have h := AxisRotation.z_orthogonal (-φ)
    rw [hneg,Matrix.transpose_transpose] at h
    simpa only [hneg] using h
  have hnom : (m.nominalThrust t).ofLp=AxisRotation.zMatrix (m.phase t) *ᵥ
      ![m.radial t,m.tangent,0] := by
    rw [nominalThrust_components m hr,pack_eq,turn_matrix]
  have hrel : (m.relativeThrust θ t).ofLp=
      ((attitude θ).val-1) *ᵥ (AxisRotation.zMatrix (m.phase t) *ᵥ ![m.radial t,m.tangent,0]) := by
    rw [Model.relativeThrust,Model.source,VaryingRateForcing.source_physical,turn_matrix]
    simp only [←Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_mulVec,hunit,Matrix.one_mulVec]
  simp only [Model.thrust,WithLp.ofLp_add,Pi.add_apply]
  rw [hnom,hrel,Matrix.sub_mulVec,Matrix.one_mulVec]
  module

structure Motion (m : Model) (θ : ℝ) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=m.reference 0
  initial_v : v 0=m.referenceVelocity 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (m.acceleration θ t (p t)) t

/-- Only the burn-interval forcing needs to be bounded. A clamped continuous
extension constructs a solution; on [0,1] the original source is restored.
The returned motion is a solution of full gravity, not a linearized field. -/
theorem Model.exists_motion (m : Model) (hμ : 0≤m.μ) (hr : 0<m.r) (θ : ℝ)
    {r0 D : ℝ} {R : ℚ} (hr0 : 0<r0) (hR : 0≤R)
    (hgain : (1/4:ℝ)*(2*m.μ/r0^3)≤1) (hregion : r0+2*(R:ℝ)≤m.r)
    (hD : 0≤D) (hforce : ∀ t ∈ Icc (0:ℝ) 1, ‖m.relativeThrust θ t‖≤D)
    (hclose : 10*D≤(R:ℝ)) :
    ∃ X : Motion m θ, ∀ t ∈ Icc (0:ℝ) 1, r0≤‖X.p t‖ := by
  let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hc : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hi (t : ℝ) : clamp t ∈ Icc (0:ℝ) 1 := by
    dsimp [clamp]
    exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have he (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : clamp t=t := by
    simp only [clamp,min_eq_right ht.2,max_eq_right ht.1]
  let d : ℝ → E3 := fun t => m.relativeThrust θ (clamp t)
  obtain ⟨x,hx,hx0,hradius,hderiv⟩ := ForcedOrbitExistence.exists_relative_four_gain
    hμ (by norm_num : (0:ℝ)≤1) hr0 hR (by simpa using hgain)
    m.reference d m.reference_continuous ((m.relativeThrust_continuous θ).comp hc)
    (by intro t; rw [m.reference_norm hr.le]; exact hregion)
    hD (fun t => hforce (clamp t) (hi t)) hclose
  refine ⟨{
    p := fun t => m.reference t+(x t).1
    v := fun t => m.referenceVelocity t+(x t).2
    continuous_p := m.reference_continuous.add hx.fst
    continuous_v := (m.referenceVelocity_continuous hr).add hx.snd
    initial_p := by simp [hx0]
    initial_v := by simp [hx0]
    derivative_p := fun t ht => (m.reference_derivative t).add (hderiv t ht).fst
    derivative_v := ?_ },hradius⟩
  intro t ht
  convert (m.referenceVelocity_derivative hr t).add (hderiv t ht).snd using 1
  dsimp [Model.acceleration,Model.thrust,ForcedOrbitExistence.rate,d]
  rw [he t ht]
  simp only [one_smul]
  module

end GNC.OrbitalComparison.VaryingRateBurn
