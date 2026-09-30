import GNC.Magnus.FohExactPreintegration

/-! Exact elementary constant-gyro force moments and actual zero/constant-gyro
velocity/position endpoints. The hypotheses are the original physical ODEs
and initial values, not assumed moment or endpoint formulas. -/
noncomputable section
open Matrix Real
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Magnus

def fohTrigMoment (δ : ℝ) : ℕ → ℝ → ℝ × ℝ
  | 0, t => (sin (δ*t)/δ, (1-cos (δ*t))/δ)
  | n+1, t => ((t^(n+1)*sin (δ*t)-(n+1)*(fohTrigMoment δ n t).2)/δ,
      ((n+1)*(fohTrigMoment δ n t).1-t^(n+1)*cos (δ*t))/δ)

theorem fohTrigMoment_initial (δ : ℝ) (n : ℕ) : fohTrigMoment δ n 0 = (0,0) := by
  induction n with
  | zero => simp [fohTrigMoment]
  | succ n ih => simp [fohTrigMoment, ih]

set_option maxHeartbeats 1000000 in
theorem fohTrigMoment_derivative (δ : ℝ) (hδ : δ ≠ 0) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun u => (fohTrigMoment δ n u).1) (t^n*cos (δ*t)) t ∧
    HasDerivAt (fun u => (fohTrigMoment δ n u).2) (t^n*sin (δ*t)) t := by
  have hs := ((hasDerivAt_id t).const_mul δ).sin
  have hc := ((hasDerivAt_id t).const_mul δ).cos
  induction n with
  | zero =>
    constructor
    · convert hs.div_const δ using 1
      simp [hδ]
    · convert (hc.const_sub 1).div_const δ using 1
      simp [hδ]
  | succ n ih =>
    constructor
    · convert (((hasDerivAt_pow (n+1) t).mul hs).sub
        (ih.2.const_mul ((n:ℝ)+1))).div_const δ using 1
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, id_eq]
      field_simp [hδ]
      ring
    · convert ((ih.1.const_mul ((n:ℝ)+1)).sub
        ((hasDerivAt_pow (n+1) t).mul hc)).div_const δ using 1
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, id_eq]
      field_simp [hδ]
      ring

def fohConstantMoment (w : Vec3) (δ : ℝ) (n : ℕ) (t : ℝ) (x : Vec3) : Vec3 :=
  (t^(n+1)/(n+1)) • x + ((fohTrigMoment δ n t).2/δ) • (skew w *ᵥ x) +
    ((t^(n+1)/(n+1)-(fohTrigMoment δ n t).1)/δ^2) • (skew w^2 *ᵥ x)

@[simp] theorem fohConstantMoment_initial (w : Vec3) (δ : ℝ) (n : ℕ) (x : Vec3) :
    fohConstantMoment w δ n 0 x = 0 := by
  simp [fohConstantMoment, fohTrigMoment_initial]

theorem foh_constant_rotation (R : ℝ → SO3) (w : Vec3)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew w) t)
    (hR0 : R 0 = 1) : R = fun t => rotationExp (t • w) := by
  apply foh_rotation_ode_unique R (fun t => rotationExp (t • w)) (fun _ => w) hR
  · intro t
    simpa using foh_fixed_axis_derivative (fun t => t) w (hasDerivAt_id t)
  · simpa [foh_rotationExp_zero] using hR0

set_option maxHeartbeats 1000000 in
theorem fohConstantMoment_derivative (w : Vec3) (δ : ℝ) (hδ : δ ≠ 0)
    (hw : skew w ^ 3 = -(δ^2) • skew w) (n : ℕ) (t : ℝ) (x : Vec3) :
    HasDerivAt (fun u => fohConstantMoment w δ n u x)
      (t^n • rotate (rotationExp (t • w)) x) t := by
  have hp : HasDerivAt (fun u : ℝ => u^(n+1)/((n:ℝ)+1)) (t^n) t := by
    convert (hasDerivAt_pow (n+1) t).div_const ((n:ℝ)+1) using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    field_simp
  have hd := fohTrigMoment_derivative δ hδ n t
  have hh := ((hp.smul_const x).add ((hd.2.div_const δ).smul_const (skew w *ᵥ x))).add
    (((hp.sub hd.1).div_const (δ^2)).smul_const (skew w^2 *ᵥ x))
  convert hh using 1
  have he : (rotationExp (t • w)).val = Preintegration.rodrigues (skew w) δ t := by
    simpa only [rotationExp, skew_smul] using Preintegration.exp_rodrigues (skew w) δ t hδ hw
  rw [rotate, he]
  simp only [Preintegration.rodrigues, Preintegration.f₁, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

/-- Reconstruction from moment primitives and the original velocity/position ODEs. -/
theorem foh_three_moment_endpoints (R : ℝ → SO3) (v p : ℝ → Vec3)
    (a b : Vec3) (I : ℕ → ℝ → Vec3 → Vec3)
    (hI : ∀ j, j ≤ 2 → ∀ t x, HasDerivAt (fun u => I j u x) (t^j • rotate (R t) x) t)
    (hI0 : ∀ j, j ≤ 2 → ∀ x, I j 0 x = 0)
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a+t • b)) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0) (T : ℝ) :
    v T = I 0 T a + I 1 T b ∧
      p T = T • (I 0 T a + I 1 T b) - I 1 T a - I 2 T b := by
  have hd (t : ℝ) : HasDerivAt (fun u => I 0 u a + I 1 u b)
      (rotate (R t) (a+t • b)) t := by
    convert (hI 0 (by omega) t a).add (hI 1 (by omega) t b) using 1
    simp [rotate, Matrix.mulVec_add, Matrix.mulVec_smul]
  have he (t : ℝ) : v t = I 0 t a + I 1 t b := by
    have hz (s : ℝ) := (hv s).sub (hd s)
    have hc := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
      (fun s => by simpa using (hz s).deriv) t 0
    exact sub_eq_zero.mp (by simpa [hv0, hI0 0 (by omega), hI0 1 (by omega)] using hc)
  refine ⟨he T, ?_⟩
  have hpd (t : ℝ) : HasDerivAt
      (fun u => u • (I 0 u a + I 1 u b)-I 1 u a-I 2 u b) (v t) t := by
    rw [he t]
    convert (((hasDerivAt_id t).smul ((hI 0 (by omega) t a).add (hI 1 (by omega) t b))).sub
      (hI 1 (by omega) t a)).sub (hI 2 (by omega) t b) using 1
    simp only [id_eq, one_smul, pow_zero, pow_one, smul_add, smul_smul, pow_two, Pi.add_apply]
    module
  have hz (s : ℝ) := (hp s).sub (hpd s)
  have hc := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
    (fun s => by simpa using (hz s).deriv) T 0
  exact sub_eq_zero.mp (by simpa [hp0, hI0 0 (by omega), hI0 1 (by omega), hI0 2 (by omega)] using hc)

/-- Exact nonzero constant-gyro FOH translation from the original physical ODEs. -/
theorem foh_constant_gyro_endpoints (R : ℝ → SO3) (v p : ℝ → Vec3)
    (w a b : Vec3) (hw : w ≠ 0)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) ((R t).val * skew w) t)
    (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a+t • b)) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0) (T : ℝ) :
    R T = rotationExp (T • w) ∧
    v T = fohConstantMoment w (enorm w) 0 T a + fohConstantMoment w (enorm w) 1 T b ∧
    p T = T • (fohConstantMoment w (enorm w) 0 T a +
      fohConstantMoment w (enorm w) 1 T b) -
      fohConstantMoment w (enorm w) 1 T a - fohConstantMoment w (enorm w) 2 T b := by
  have he := foh_constant_rotation R w hR hR0
  refine ⟨congrFun he T, ?_⟩
  apply foh_three_moment_endpoints R v p a b (fohConstantMoment w (enorm w)) _
    (fun j _ => fohConstantMoment_initial w (enorm w) j) hv hv0 hp hp0 T
  intro j _ t x
  rw [he]
  exact fohConstantMoment_derivative w (enorm w) ((enorm_eq_zero_iff w).not.mpr hw)
    (skew_cube w) j t x

/-- Exact zero-gyro branch, including position and affine acceleration. -/
theorem foh_zero_gyro_endpoints (R : ℝ → SO3) (v p : ℝ → Vec3) (a b : Vec3)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val) 0 t) (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a+t • b)) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0) (T : ℝ) :
    R T = 1 ∧ v T = T • a + (T^2/2) • b ∧
      p T = (T^2/2) • a + (T^3/6) • b := by
  have he : R = fun _ => 1 := by
    have hh := foh_constant_rotation R 0 (by simpa [skew_zero] using hR) hR0
    simpa only [smul_zero, foh_rotationExp_zero] using hh
  let I : ℕ → ℝ → Vec3 → Vec3 := fun j t x => (t^(j+1)/(j+1)) • x
  have hd (j : ℕ) (t : ℝ) (x : Vec3) :
      HasDerivAt (fun u => I j u x) (t^j • rotate (R t) x) t := by
    rw [he]
    have hh : HasDerivAt (fun u : ℝ => u^(j+1)/((j:ℝ)+1)) (t^j) t := by
      convert (hasDerivAt_pow (j+1) t).div_const ((j:ℝ)+1) using 1
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      field_simp
    simpa [I, rotate] using hh.smul_const x
  have hh := foh_three_moment_endpoints R v p a b I (fun j _ => hd j)
    (by intro j _ x; simp [I]) hv hv0 hp hp0 T
  refine ⟨congrFun he T, ?_, ?_⟩
  · simpa [I, show (1:ℝ)+1=2 by norm_num] using hh.1
  · rw [hh.2]
    simp only [I, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
    norm_num
    module

/-- Complex packaging of the elementary sine/cosine moments. -/
def fohConstantF (δ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (fohTrigMoment δ n t).1 + (fohTrigMoment δ n t).2 * Complex.I

theorem fohConstantF_zero (δ : ℝ) (hδ : δ ≠ 0) (t : ℝ) :
    fohConstantF δ 0 t = (Complex.exp ((δ*t:ℝ)*Complex.I)-1)/(Complex.I*δ) := by
  apply (eq_div_iff (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hδ))).mpr
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext <;> simp [fohConstantF, fohTrigMoment, Complex.mul_re, Complex.mul_im]
  all_goals field_simp [hδ] <;> ring

theorem fohConstantF_succ (δ : ℝ) (hδ : δ ≠ 0) (n : ℕ) (t : ℝ) :
    fohConstantF δ (n+1) t =
      ((t:ℂ)^(n+1)*Complex.exp ((δ*t:ℝ)*Complex.I) - (n+1)*fohConstantF δ n t) /
        (Complex.I*δ) := by
  apply (eq_div_iff (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hδ))).mpr
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext <;> simp [fohConstantF, fohTrigMoment, Complex.mul_re, Complex.mul_im]
  all_goals field_simp [hδ] <;> ring

end GNC.Magnus
