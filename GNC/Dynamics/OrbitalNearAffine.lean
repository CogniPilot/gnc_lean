import GNC.Dynamics.MatrixDynamics
import GNC.Dynamics.GravityRemainderBall
import GNC.Dynamics.LieErrorReconstruction
import GNC.Analysis.EuclideanBox
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact shared-input orbital log dynamics, with an explicit gravity-only
nonlinear remainder. The finite-region estimate below uses attitude error
at most one radian (a stated domain, not a numerical tolerance). Neither
thrust acceleration nor angular velocity enters its coefficient. They do
enter the retained linear operator and therefore its STM and tube gains.
-/
noncomputable section
open Matrix Real
namespace GNC.OrbitalNearAffine

def gradient (μ : ℝ) (R : SO3) (q v : Vec3) : Vec3 :=
  Gravity.radialMap (μ/enorm q^3) (Jacobian.unitAxis (rotate R⁻¹ q)) v

def residual (μ : ℝ) (R : SO3) (q : Vec3) (x : LogState) : Vec3 :=
  Jacobian.inverseAt (x 2) (rotate R⁻¹
    (Gravity.field3 μ (q+rotate R (Jacobian.leftAt (x 2) (x 0)))-Gravity.field3 μ q))
    -gradient μ R q (x 0)

def linearPart (μ : ℝ) (R : SO3) (q : Vec3) (ν x : LogState) : LogState :=
  logDrift ν x+velocityOnly (gradient μ R q (x 0))

def linearMap (μ : ℝ) (R : SO3) (q : Vec3) (ν : LogState) : LogState →ₗ[ℝ] LogState where
  toFun := linearPart μ R q ν
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [linearPart, logDrift, ad, velocityOnly, gradient, Gravity.radialMap,
        cross_apply, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [linearPart, logDrift, ad, velocityOnly, gradient, Gravity.radialMap,
        cross_apply, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

def operator (μ : ℝ) (R : SO3) (q : Vec3) (ν : LogState) : LogState →L[ℝ] LogState :=
  (linearMap μ R q ν).toContinuousLinearMap

theorem reconstruction {X Y : SE23} {x : LogState} (he : SE23.error Y X=groupExp x) :
    X=Y*groupExp x := by
  rw [←he, SE23.error, ←mul_assoc, mul_inv_cancel, one_mul]

/-- Derived from the physical matrix equations, not assumed log dynamics.
Time-varying shared inputs are allowed by applying this pointwise. -/
theorem log_equation (μ : ℝ) {X Y : ℝ → SE23} {x : ℝ → LogState}
    {dx ν : LogState} {t : ℝ}
    (hX : HasDerivAt (fun s => SE23.toMatrix (X s))
      (spacecraftDerivative (X t) ν (Gravity.field3 μ (X t).pos)) t)
    (hY : HasDerivAt (fun s => SE23.toMatrix (Y s))
      (spacecraftDerivative (Y t) ν (Gravity.field3 μ (Y t).pos)) t)
    (hx : HasDerivAt x dx t) (he : ∀ s, SE23.error (Y s) (X s)=groupExp (x s))
    (hangle : enorm (x t 2)<π) :
    dx=operator μ (Y t).rot (Y t).pos ν (x t)+
      velocityOnly (residual μ (Y t).rot (Y t).pos (x t)) := by
  have h := spacecraft_log_equation hX hY hx he hangle
  simp only [sub_self, zero_add, Jacobian.blockInverse_velocityOnly] at h
  have hp := congrArg SE23.pos (reconstruction (he t))
  rw [hp] at h
  rw [h]
  ext i j
  fin_cases i <;> simp [operator, linearMap, linearPart, residual, velocityOnly,
    SE23.mul_pos, groupExp] <;> abel

/-- The navigation limit is exactly linear for shared prescribed gravity,
even if that common gravity and the shared input vary with time. -/
theorem uniform_gravity_log_equation {X Y : ℝ → SE23} {x : ℝ → LogState}
    {dx ν : LogState} {g : Vec3} {t : ℝ}
    (hX : HasDerivAt (fun s => SE23.toMatrix (X s)) (spacecraftDerivative (X t) ν g) t)
    (hY : HasDerivAt (fun s => SE23.toMatrix (Y s)) (spacecraftDerivative (Y t) ν g) t)
    (hx : HasDerivAt x dx t) (he : ∀ s, SE23.error (Y s) (X s)=groupExp (x s))
    (hangle : enorm (x t 2)<π) : dx=logDrift ν (x t) := by
  have h := spacecraft_log_equation hX hY hx he hangle
  have hz : velocityOnly (0:Vec3)=0 := by ext i j; fin_cases i <;> rfl
  have hJ : Jacobian.blockInverse (x t) 0=0 := by
    ext i j
    fin_cases i <;> simp [Jacobian.blockInverse]
  simpa only [sub_self, zero_add, rotate_zero, Jacobian.blockInverse_velocityOnly,
    Jacobian.inverseAt_zero, hz, hJ, add_zero] using h

theorem residual_axis (μ : ℝ) (R : SO3) (q : Vec3) (x : LogState)
    (hq : 0<enorm q) (k : Vec3) (hk : k ⬝ᵥ k=1) {θ : ℝ} (hθ : 0<θ)
    (hx : x 2=θ • k) :
    residual μ R q x =
      Gravity.attitudeResidual (μ/enorm q^3) (Jacobian.unitAxis (rotate R⁻¹ q)) k θ (x 0)+
      Gravity.higherGravity μ R q k θ (x 0) := by
  have h := Gravity.gravity_decomposition μ R q k (x 0) hq hk θ hθ
  unfold residual gradient
  rw [hx, Jacobian.inverseAt_axis k _ hk θ hθ]
  change Gravity.bodyGravity μ R q k θ (x 0)-_=_
  rw [h]
  abel

/-- Uniform inverse-Jacobian gain on the explicitly chosen one-radian chart. -/
theorem inverse_gain {θ : ℝ} (hθ : 0<θ) (hθ1 : θ≤1) :
    (θ/2)/sin (θ/2) ≤ 4/3 := by
  have hs := Real.sin_gt_sub_cube (x := θ/2) (by linarith) (by linarith)
  have hpow : (θ/2)^3 ≤ θ/2 := by nlinarith [sq_nonneg (θ/2), mul_nonneg hθ.le (sub_nonneg.mpr hθ1)]
  have hl : 3*θ/8 ≤ sin (θ/2) := by linarith
  apply (div_le_iff₀ (by linarith : 0<sin (θ/2))).mpr
  linarith

theorem attitude_bound {l θ : ℝ} (hl : 0≤l) (hθ : 0<θ) (hθ1 : θ≤1)
    (r k v : Vec3) (hr : r ⬝ᵥ r=1) (hk : k ⬝ᵥ k=1) :
    enorm (Gravity.attitudeResidual l r k θ v) ≤ 2*l*θ*enorm v := by
  have hπ : θ<π := hθ1.trans_lt (by linarith [Real.pi_gt_three])
  have hb := Gravity.attitudeResidual_bound l hl r k v hr hk θ hθ hπ
  have hspos : 0<sin (θ/2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hgain := inverse_gain hθ hθ1
  have hslo : 3*θ/8 ≤ sin (θ/2) := by
    have hi := (div_le_iff₀ hspos).mp hgain
    linarith
  have htail : θ-sin θ ≤ θ^3/4 := by
    linarith [Real.sin_gt_sub_cube hθ hθ1]
  have hquot : (θ-sin θ)/(4*sin (θ/2)) ≤ θ/6 := by
    apply (div_le_iff₀ (by positivity : 0<4*sin (θ/2))).mpr
    have hmul := mul_le_mul_of_nonneg_left hslo (show 0≤θ*2/3 by positivity)
    have hcube : θ^3≤θ^2 := by nlinarith [mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr hθ1)]
    nlinarith
  have ha : sin (θ/2)*sin (Gravity.separationAngle k r) ≤ θ/2 :=
    (mul_le_mul_of_nonneg_left (sin_le_one _) hspos.le).trans (by simpa using sin_le (by linarith : 0≤θ/2))
  have hb' : (θ-sin θ)/(4*sin (θ/2))*|sin (2*Gravity.separationAngle k r)| ≤ θ/6 :=
    (mul_le_mul_of_nonneg_left (abs_sin_le_one _) (div_nonneg
      (sub_nonneg.mpr (sin_le hθ.le)) (by positivity))).trans (by simpa using hquot)
  have hh := mul_le_mul_of_nonneg_left (add_le_add ha hb') (show 0≤3*l by positivity)
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hh (enorm_nonneg v)])

/-- A regional, quadratic spatial-gravity bound combined with the exact
attitude/gradient commutator. Valid also at zero attitude error. -/
theorem residual_bound (μ : ℝ) (hμ : 0≤μ) (R : SO3) (q : Vec3) (x : LogState)
    {r D : ℝ} (hD : D<r) (hq : r≤enorm q)
    (hp : enorm (x 0)≤D) (hangle : enorm (x 2)≤1) :
    enorm (residual μ R q x) ≤
      2*(μ/enorm q^3)*enorm (x 2)*enorm (x 0)+
      (4*μ/(r-D)^4)*enorm (x 0)^2 := by
  have hq0 : 0<enorm q := lt_of_le_of_lt (enorm_nonneg _) (hp.trans_lt (hD.trans_le hq))
  have hπ : enorm (x 2)<π := hangle.trans_lt (by linarith [Real.pi_gt_three])
  let d := rotate R (Jacobian.leftAt (x 2) (x 0))
  have hd : enorm d≤enorm (x 0) := by
    dsimp [d]; rw [rotate_enorm]
    exact leftAt_nonexpansive _ _ (by linarith [pi_pos])
  have hg : enorm (Gravity.remainder3 μ q d) ≤
      (3*μ/(r-D)^4)*enorm (x 0)^2 := by
    exact (Gravity.remainder_quadratic μ hμ
      (WithLp.toLp 2 q : Jacobian.E3) (WithLp.toLp 2 d)
      hD hq (hd.trans hp)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (enorm_nonneg d) hd 2) (by positivity))
  by_cases hz : x 2=0
  · have hid : residual μ R q x=rotate R⁻¹ (Gravity.remainder3 μ q d) := by
      unfold residual gradient Gravity.remainder3 d
      rw [←Gravity.gradient3_body μ R q (x 0) hq0]
      simp [hz, Jacobian.inverseAt, Jacobian.leftAt, rotate_sub]
    rw [hid, rotate_enorm]
    have he : enorm (x 2)=0 := (enorm_eq_zero_iff _).mpr hz
    rw [he]
    have hh : (3*μ/(r-D)^4)*enorm (x 0)^2 ≤
        (4*μ/(r-D)^4)*enorm (x 0)^2 := by
      gcongr; linarith
    simpa using hg.trans hh
  · have hθ : 0<enorm (x 2) := lt_of_le_of_ne (enorm_nonneg _) (Ne.symm
      (fun h => hz ((enorm_eq_zero_iff _).mp h)))
    let k := Jacobian.unitAxis (x 2)
    have hk : k ⬝ᵥ k=1 := Jacobian.unitAxis_unit _ hθ
    have hx : x 2=enorm (x 2) • k := (Jacobian.unitAxis_reconstruct _ hθ).symm
    have hr : Jacobian.unitAxis (rotate R⁻¹ q) ⬝ᵥ Jacobian.unitAxis (rotate R⁻¹ q)=1 :=
      Jacobian.unitAxis_unit _ (by simpa only [rotate_enorm] using hq0)
    have ha := attitude_bound (show 0≤μ/enorm q^3 by positivity) hθ hangle
      (Jacobian.unitAxis (rotate R⁻¹ q)) k (x 0) hr hk
    have hh : enorm (Gravity.higherGravity μ R q k (enorm (x 2)) (x 0)) ≤
        (4*μ/(r-D)^4)*enorm (x 0)^2 := by
      have he : physicalImpulse R (enorm (x 2) • k) (x 0)=d := by
        rw [←hx]; rfl
      unfold Gravity.higherGravity
      rw [he]
      have hi := Jacobian.leftInv_bound k
        (rotate R⁻¹ (Gravity.remainder3 μ q d)) hk (enorm (x 2)) hθ (by linarith)
      rw [rotate_enorm] at hi
      have hgain := inverse_gain hθ hangle
      have hg0 : 0≤(3*μ/(r-D)^4)*enorm (x 0)^2 := by positivity
      exact hi.trans ((mul_le_mul hgain hg (enorm_nonneg _) (by norm_num)).trans_eq (by ring))
    rw [residual_axis μ R q x hq0 k hk hθ hx]
    exact (enorm_add_le _ _).trans (add_le_add ha hh)

/-- The remainder vanishes identically when gravity is removed; there is
no hidden finite-angle thrust remainder in this expression. -/
theorem residual_zero_gravity (R : SO3) (q : Vec3) (x : LogState) :
    residual 0 R q x=0 := by
  simp [residual, gradient, Gravity.field3, Gravity.field, Gravity.radialMap,
    Jacobian.inverseAt]

end GNC.OrbitalNearAffine
