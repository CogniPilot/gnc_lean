import GNC.Dynamics.OrbitalNearAffine
import GNC.Dynamics.ReactionWheels
import GNC.Dynamics.LieRadiusCertificate

/-! Candidate-side certification of a geometric lift of an angle STM.
For a fixed inertial attitude offset phi and any prescribed thrust history,
the ordinary angle response y''=G(t)y+phi x u(t) is lifted as q+J(phi)y.
The identity charges computed reference and response defects explicitly.
Only the gravity commutator and spatial curvature remain when those defects
vanish. This is not a claim that exact-component Cartesian STTs have the
same remainder; they avoid this commutator by retaining a different response.
-/
noncomputable section
open Matrix Real
namespace GNC.GeometricSTMDefect

/-- Exact moving-frame reduction of the retained log model. Its inertial
translation is the ordinary angle STM response; the finite-angle geometry
enters in reconstruction. Angular velocity cancels here by differentiation,
not by assuming an inertially fixed reference attitude. -/
theorem retained_world_equation (μ : ℝ) {R : ℝ → SO3} {x : ℝ → LogState}
    {dx : LogState} {q a w : Vec3} {t : ℝ} (hq : 0<enorm q)
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*skew w) t)
    (hx : HasDerivAt x dx t)
    (hd : dx=OrbitalNearAffine.operator μ (R t) q ![0,a,w] (x t)) :
    HasDerivAt (fun s => rotate (R s) (x s 0)) (rotate (R t) (x t 1)) t ∧
    HasDerivAt (fun s => rotate (R s) (x s 1))
      (Gravity.gradient3 μ q (rotate (R t) (x t 0))+
        rotate (R t) (x t 2) ⨯₃ rotate (R t) a) t ∧
    HasDerivAt (fun s => rotate (R s) (x s 2)) 0 t := by
  have hcomp (i : Fin 3) : HasDerivAt (fun s => x s i) (dx i) t :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Vec3) i).hasFDerivAt.comp_hasDerivAt t hx
  have h0 := ReactionWheels.rotate_derivative hR (hcomp 0)
  have h1 := ReactionWheels.rotate_derivative hR (hcomp 1)
  have h2 := ReactionWheels.rotate_derivative hR (hcomp 2)
  have hg := Gravity.gradient3_body μ (R t) q (x t 0) hq
  change rotate (R t)⁻¹ (Gravity.gradient3 μ q (rotate (R t) (x t 0)))=
    OrbitalNearAffine.gradient μ (R t) q (x t 0) at hg
  have hd0 : dx 0+w ⨯₃ x t 0=x t 1 := by
    rw [hd]; simp [OrbitalNearAffine.operator, OrbitalNearAffine.linearMap,
      OrbitalNearAffine.linearPart, logDrift, ad, velocityOnly]
  have hd1 : dx 1+w ⨯₃ x t 1=
      OrbitalNearAffine.gradient μ (R t) q (x t 0)+x t 2 ⨯₃ a := by
    rw [hd]
    ext i
    fin_cases i <;> simp [OrbitalNearAffine.operator, OrbitalNearAffine.linearMap,
      OrbitalNearAffine.linearPart, logDrift, ad, velocityOnly, cross_apply,
      Matrix.vecHead, Matrix.vecTail] <;> ring
  have hd2 : dx 2+w ⨯₃ x t 2=0 := by
    rw [hd]; simp [OrbitalNearAffine.operator, OrbitalNearAffine.linearMap,
      OrbitalNearAffine.linearPart, logDrift, ad, velocityOnly]
  rw [hd0] at h0
  rw [hd1, rotate_add, ←hg, ←rotate_mul, mul_inv_cancel, rotate_one, rotate_cross] at h1
  rw [hd2, rotate_zero] at h2
  exact ⟨h0,h1,h2⟩

/-- The physical translation of the retained log predictor uses the same
inertial response as an angle STM, followed by the exact Jacobian. -/
theorem world_reconstruction (R : SO3) (x : LogState) :
    rotate R (Jacobian.leftAt (x 2) (x 0))=
      Jacobian.leftAt (rotate R (x 2)) (rotate R (x 0)) :=
  (leftAt_rotation_equivariant R (x 2) (x 0)).symm

def defect (μ : ℝ) (φ q y u qdd ydd : Vec3) : Vec3 :=
  Gravity.field3 μ (q+Jacobian.leftAt φ y)+rotate (rotationExp φ) u-
    (qdd+Jacobian.leftAt φ ydd)

/-- In the gravity-free limit the ideal geometric predictor has exactly
zero acceleration defect at every angle, not just to some Taylor order. -/
theorem zero_gravity_defect (φ q y u : Vec3) :
    defect 0 φ q y u u (φ ⨯₃ u)=0 := by
  simp [defect, Gravity.field3, Gravity.field, leftAt_cross_rotation]

/-- Valid for numerical candidates as well as exact linear responses. -/
theorem split (μ : ℝ) (φ q y u qdd ydd : Vec3)
    (hq : 0<enorm q) (hφ : enorm φ<2*π) :
    defect μ φ q y u qdd ydd =
      (Gravity.field3 μ q+u-qdd)+
      Jacobian.leftAt φ (Gravity.gradient3 μ q y+φ ⨯₃ u-ydd)+
      Jacobian.leftAt φ (OrbitalNearAffine.residual μ 1 q ![y,0,φ]) := by
  have hg := Gravity.gradient3_body μ 1 q y hq
  have h0 : (![y,(0:Vec3),φ] : LogState) 0=y := rfl
  have h2 : (![y,(0:Vec3),φ] : LogState) 2=φ := rfl
  simp only [inv_one, rotate_one] at hg
  dsimp only [defect, OrbitalNearAffine.residual, OrbitalNearAffine.gradient]
  simp only [h0, h2, inv_one, rotate_one,
    Jacobian.leftAt_add, Jacobian.leftAt_sub, Jacobian.leftAt_inverseAt_all φ _ hφ,
    leftAt_cross_rotation]
  rw [←hg]
  abel

/-- Physical defect bound; no inverse Jacobian is applied to numerical
errors because the forward Jacobian is nonexpansive. -/
theorem bound (μ : ℝ) (hμ : 0≤μ) (φ q y u qdd ydd : Vec3)
    {r D εref εresponse : ℝ} (hD : D<r) (hq : r≤enorm q)
    (hy : enorm y≤D) (hφ : enorm φ≤1)
    (href : enorm (Gravity.field3 μ q+u-qdd)≤εref)
    (hresponse : enorm (Gravity.gradient3 μ q y+φ ⨯₃ u-ydd)≤εresponse) :
    enorm (defect μ φ q y u qdd ydd) ≤ εref+εresponse+
      2*(μ/enorm q^3)*enorm φ*enorm y+(4*μ/(r-D)^4)*enorm y^2 := by
  have hq0 : 0<enorm q := lt_of_le_of_lt (enorm_nonneg y) (hy.trans_lt (hD.trans_le hq))
  have hφπ : enorm φ<2*π := by linarith [Real.pi_gt_three]
  rw [split μ φ q y u qdd ydd hq0 hφπ]
  have hb := OrbitalNearAffine.residual_bound μ hμ 1 q ![y,0,φ] hD hq hy hφ
  change enorm (OrbitalNearAffine.residual μ 1 q ![y,0,φ]) ≤
    2*(μ/enorm q^3)*enorm φ*enorm y+(4*μ/(r-D)^4)*enorm y^2 at hb
  have hr := (leftAt_nonexpansive φ _ hφπ).trans hb
  have hs := (leftAt_nonexpansive φ _ hφπ).trans hresponse
  have ht := (enorm_add_le _ _).trans (add_le_add
    ((enorm_add_le _ _).trans (add_le_add href hs)) hr)
  convert ht using 1
  dsimp only
  ring

/-- Keep the known t^2 growth of the retained response. The two physical
sources are t^2 and t^4, rather than constant endpoint allowances. -/
theorem time_profile (μ : ℝ) (hμ : 0≤μ) (φ q y u qdd ydd : Vec3)
    {r D L θ t εref εresponse : ℝ} (hr : 0<r) (hD : D<r)
    (hL : 0≤L) (ht : 0≤t) (ht1 : t≤1) (hLD : L≤D)
    (hq : r≤enorm q) (hy : enorm y≤L*t^2)
    (hφ : enorm φ≤θ) (hθ : θ≤1)
    (href : enorm (Gravity.field3 μ q+u-qdd)≤εref)
    (hresponse : enorm (Gravity.gradient3 μ q y+φ ⨯₃ u-ydd)≤εresponse) :
    enorm (defect μ φ q y u qdd ydd) ≤ εref+εresponse+
      (2*μ/r^3*θ*L)*t^2+(4*μ/(r-D)^4*L^2)*t^4 := by
  have hq0 : 0<enorm q := hr.trans_le hq
  have hy0 := enorm_nonneg y
  have hφ0 := enorm_nonneg φ
  have hθ0 := hφ0.trans hφ
  have hcoef : μ/enorm q^3≤μ/r^3 :=
    div_le_div_of_nonneg_left hμ (by positivity) (pow_le_pow_left₀ hr.le hq 3)
  have hyD : enorm y≤D := hy.trans ((mul_le_mul_of_nonneg_left
    (show t^2≤1 by nlinarith) hL).trans (by simpa using hLD))
  have hb := bound μ hμ φ q y u qdd ydd hD hq hyD (hφ.trans hθ) href hresponse
  have h1 : 2*(μ/enorm q^3)*enorm φ*enorm y ≤ 2*(μ/r^3)*θ*(L*t^2) := by
    gcongr
  have h2 : (4*μ/(r-D)^4)*enorm y^2 ≤ (4*μ/(r-D)^4)*(L*t^2)^2 := by
    gcongr
  calc
    _ ≤ εref+εresponse+2*(μ/r^3)*θ*(L*t^2)+(4*μ/(r-D)^4)*(L*t^2)^2 :=
      hb.trans (add_le_add (add_le_add le_rfl h1) h2)
    _ = _ := by ring

end GNC.GeometricSTMDefect
