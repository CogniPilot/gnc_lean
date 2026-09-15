import GNC.Lie.AxisRotation
import GNC.Analysis.SymplecticResponse

/-! Product angular velocity and acceleration, with Euclidean bounds.
The cross term from a moving body frame is retained explicitly. -/
noncomputable section
set_option autoImplicit false
namespace GNC.RotationKinematics
open Matrix
open scoped Matrix Matrix.Norms.Operator

theorem inverse_transpose (R : SO3) : (R⁻¹).val = R.val.transpose := rfl

theorem inverse_derivative {R : ℝ → SO3} {w : Vec3} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*skew w) t) :
    HasDerivAt (fun s => ((R s)⁻¹).val) (-skew w*((R t)⁻¹).val) t := by
  simp only [inverse_transpose]
  convert SymplecticFlow.transpose_derivative hR using 1
  rw [transpose_mul, skew_transpose]

theorem inverse_rotate_derivative {R : ℝ → SO3} {x : ℝ → Vec3} {w v : Vec3} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*skew w) t)
    (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => rotate (R s)⁻¹ (x s))
      (rotate (R t)⁻¹ v-w ⨯₃ rotate (R t)⁻¹ (x t)) t := by
  convert SymplecticResponse.mulVec_derivative (inverse_derivative hR) hx using 1
  simp only [rotate, Matrix.neg_mul, Matrix.neg_mulVec, ← mulVec_mulVec, skew_mulVec]
  abel

def productRate (B : SO3) (a b : Vec3) : Vec3 := rotate B⁻¹ a+b
def productAcceleration (B : SO3) (a b a' b' : Vec3) : Vec3 :=
  rotate B⁻¹ a'-b ⨯₃ rotate B⁻¹ a+b'

theorem productRate_derivative {B : ℝ → SO3} {a b : ℝ → Vec3} {a' b' : Vec3} {t : ℝ}
    (hB : HasDerivAt (fun s => (B s).val) ((B t).val*skew (b t)) t)
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => productRate (B s) (a s) (b s))
      (productAcceleration (B t) (a t) (b t) a' b') t :=
  (inverse_rotate_derivative hB ha).fun_add hb

theorem productRate_bound (B : SO3) (a b : Vec3) :
    enorm (productRate B a b) ≤ enorm a+enorm b := by
  simpa [productRate, rotate_enorm] using enorm_add_le (rotate B⁻¹ a) b

theorem productAcceleration_bound (B : SO3) (a b a' b' : Vec3) :
    enorm (productAcceleration B a b a' b') ≤ enorm a'+enorm b*enorm a+enorm b' := by
  have h := (enorm_add_le (rotate B⁻¹ a'-b ⨯₃ rotate B⁻¹ a) b').trans
    (add_le_add (by simpa only [sub_eq_add_neg] using
      (enorm_add_le (rotate B⁻¹ a') (-(b ⨯₃ rotate B⁻¹ a)))) le_rfl)
  simp only [enorm_neg, rotate_enorm] at h
  exact h.trans (add_le_add (add_le_add le_rfl
    (by simpa only [rotate_enorm] using cross_enorm_le b (rotate B⁻¹ a))) le_rfl)

theorem x_axis_norm (d : ℝ) : enorm (![d,0,0]) = |d| := by
  have h := enorm_sq (![d,0,0])
  simp [lengthSq] at h
  nlinarith [enorm_nonneg (![d,0,0]), abs_nonneg d, sq_abs d]

theorem z_axis_norm (d : ℝ) : enorm (![0,0,d]) = |d| := by
  have h := enorm_sq (![0,0,d])
  simp [lengthSq] at h
  nlinarith [enorm_nonneg (![0,0,d]), abs_nonneg d, sq_abs d]

structure Path where
  rotation : ℝ → SO3
  velocity : ℝ → Vec3
  acceleration : ℝ → Vec3

def Path.HasJet (p : Path) (t : ℝ) : Prop :=
  HasDerivAt (fun s => (p.rotation s).val) ((p.rotation t).val*skew (p.velocity t)) t ∧
    HasDerivAt p.velocity (p.acceleration t) t

def Path.compose (p q : Path) : Path where
  rotation t := p.rotation t*q.rotation t
  velocity t := productRate (q.rotation t) (p.velocity t) (q.velocity t)
  acceleration t := productAcceleration (q.rotation t) (p.velocity t) (q.velocity t)
    (p.acceleration t) (q.acceleration t)

theorem Path.compose_jet (p q : Path) {t : ℝ} (hp : p.HasJet t) (hq : q.HasJet t) :
    (p.compose q).HasJet t :=
  ⟨AxisRotation.product_derivative hp.1 hq.1, productRate_derivative hq.1 hp.2 hq.2⟩

def Path.x (angle velocity acceleration : ℝ → ℝ) : Path where
  rotation t := AxisRotation.xRotation (angle t)
  velocity t := ![velocity t,0,0]
  acceleration t := ![acceleration t,0,0]
def Path.z (angle velocity acceleration : ℝ → ℝ) : Path where
  rotation t := AxisRotation.zRotation (angle t)
  velocity t := ![0,0,velocity t]
  acceleration t := ![0,0,acceleration t]

theorem Path.x_jet {angle velocity acceleration : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt angle (velocity t) t) (hv : HasDerivAt velocity (acceleration t) t) :
    (Path.x angle velocity acceleration).HasJet t := by
  refine ⟨AxisRotation.x_derivative ha, ?_⟩
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hv
  · exact hasDerivAt_const t (0:ℝ)
  · exact hasDerivAt_const t (0:ℝ)

theorem Path.z_jet {angle velocity acceleration : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt angle (velocity t) t) (hv : HasDerivAt velocity (acceleration t) t) :
    (Path.z angle velocity acceleration).HasJet t := by
  refine ⟨AxisRotation.z_derivative ha, ?_⟩
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const t (0:ℝ)
  · exact hasDerivAt_const t (0:ℝ)
  · exact hv

theorem Path.compose_bounds (p q : Path) (t : ℝ) {v w a b : ℝ}
    (hpv : enorm (p.velocity t) ≤ v) (hqv : enorm (q.velocity t) ≤ w)
    (hpa : enorm (p.acceleration t) ≤ a) (hqa : enorm (q.acceleration t) ≤ b) :
    enorm ((p.compose q).velocity t) ≤ v+w ∧
      enorm ((p.compose q).acceleration t) ≤ a+w*v+b := by
  constructor
  · exact (productRate_bound _ _ _).trans (add_le_add hpv hqv)
  · apply (productAcceleration_bound _ _ _ _ _).trans
    exact add_le_add (add_le_add hpa
      (mul_le_mul hqv hpv (enorm_nonneg _) ((enorm_nonneg _).trans hqv))) hqa

def Path.rescale (p : Path) (scale : ℝ) : Path where
  rotation s := p.rotation (s/scale)
  velocity s := (1/scale) • p.velocity (s/scale)
  acceleration s := (1/scale^2) • p.acceleration (s/scale)

theorem Path.rescale_jet (p : Path) (scale s : ℝ) (hp : p.HasJet (s/scale)) :
    (p.rescale scale).HasJet s := by
  have hr := hp.1.scomp s ((hasDerivAt_id s).div_const scale)
  have hv := hp.2.scomp s ((hasDerivAt_id s).div_const scale)
  constructor
  · convert hr using 1
    simp [Path.rescale, skew_smul, Matrix.mul_smul]
  · convert hv.const_smul (1/scale) using 1
    simp [Path.rescale, smul_smul, div_pow, pow_two]

def Path.HasContinuousJet (p : Path) : Prop :=
  Continuous (fun t => (p.rotation t).val) ∧ Continuous p.velocity ∧ Continuous p.acceleration

theorem Path.compose_continuous (p q : Path) (hp : p.HasContinuousJet) (hq : q.HasContinuousJet) :
    (p.compose q).HasContinuousJet := by
  refine ⟨hp.1.mul hq.1, ?_, ?_⟩
  · change Continuous (fun t => rotate (q.rotation t)⁻¹ (p.velocity t)+q.velocity t)
    simp only [rotate, inverse_transpose]
    exact (hq.1.matrix_transpose.matrix_mulVec hp.2.1).add hq.2.1
  · change Continuous (fun t => rotate (q.rotation t)⁻¹ (p.acceleration t)-
      q.velocity t ⨯₃ rotate (q.rotation t)⁻¹ (p.velocity t)+q.acceleration t)
    simp only [rotate, inverse_transpose]
    have ha := hq.1.matrix_transpose.matrix_mulVec hp.2.2
    have hv := hq.1.matrix_transpose.matrix_mulVec hp.2.1
    have hqv := hq.2.1
    have hc : Continuous (fun t => q.velocity t ⨯₃ ((q.rotation t).val.transpose *ᵥ p.velocity t)) := by
      apply continuous_pi
      intro i
      fin_cases i <;> simp [cross_apply, Matrix.vecHead, Matrix.vecTail] <;> fun_prop
    exact (ha.sub hc).add hq.2.2

theorem Path.x_continuous {angle velocity acceleration : ℝ → ℝ}
    (ha : ∀ t, HasDerivAt angle (velocity t) t)
    (hv : ∀ t, HasDerivAt velocity (acceleration t) t) (hc : Continuous acceleration) :
    (Path.x angle velocity acceleration).HasContinuousJet := by
  refine ⟨continuous_iff_continuousAt.mpr (fun t => (Path.x_jet (ha t) (hv t)).1.continuousAt),
    continuous_iff_continuousAt.mpr (fun t => (Path.x_jet (ha t) (hv t)).2.continuousAt), ?_⟩
  apply continuous_pi
  intro i
  fin_cases i
  · exact hc
  · exact continuous_const
  · exact continuous_const

theorem Path.z_continuous {angle velocity acceleration : ℝ → ℝ}
    (ha : ∀ t, HasDerivAt angle (velocity t) t)
    (hv : ∀ t, HasDerivAt velocity (acceleration t) t) (hc : Continuous acceleration) :
    (Path.z angle velocity acceleration).HasContinuousJet := by
  refine ⟨continuous_iff_continuousAt.mpr (fun t => (Path.z_jet (ha t) (hv t)).1.continuousAt),
    continuous_iff_continuousAt.mpr (fun t => (Path.z_jet (ha t) (hv t)).2.continuousAt), ?_⟩
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_const
  · exact hc

theorem Path.rescale_continuous (p : Path) (hp : p.HasContinuousJet) (scale : ℝ) :
    (p.rescale scale).HasContinuousJet :=
  ⟨hp.1.comp (continuous_id.div_const scale),
    (hp.2.1.comp (continuous_id.div_const scale)).const_smul _,
    (hp.2.2.comp (continuous_id.div_const scale)).const_smul _⟩

end GNC.RotationKinematics
