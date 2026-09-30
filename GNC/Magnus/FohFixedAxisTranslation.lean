import GNC.Magnus.FohDegenerateTranslation
import GNC.Magnus.FohGaussianMoment

/-! Exact fixed-axis FOH preintegration. The Gaussian primitive supplies the
zeroth oscillatory moment; integration by parts supplies the next two.
Actual rotation, velocity and position follow from their original ODEs.
The final constant-axis corollary uses only elementary trigonometric kernels. -/
noncomputable section
open Matrix Real
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Magnus
local instance : ContinuousSMul ℝ ℂ := ⟨by
  simpa only [Complex.real_smul] using
    (Complex.continuous_ofReal.comp (continuous_fst : Continuous (fun p : ℝ × ℂ => p.1))).mul continuous_snd⟩


def fohAxisPhase (δ β t : ℝ) : ℝ := δ*t+β*t^2/2

def fohAxisH (δ β t : ℝ) : ℂ := Complex.exp ((fohAxisPhase δ β t : ℝ)*Complex.I)

def fohAxisF1 (F₀ : ℝ → ℂ) (δ β t : ℝ) : ℂ :=
  (fohAxisH δ β t-1)/(Complex.I*β)-(δ:ℂ)/β*F₀ t

def fohAxisF2 (F₀ : ℝ → ℂ) (δ β t : ℝ) : ℂ :=
  ((t:ℂ)*fohAxisH δ β t-F₀ t)/(Complex.I*β)-(δ:ℂ)/β*fohAxisF1 F₀ δ β t

theorem fohAxisPhase_derivative (δ β t : ℝ) :
    HasDerivAt (fohAxisPhase δ β) (δ+β*t) t := by
  convert ((hasDerivAt_id t).const_mul δ).add
    (((hasDerivAt_pow 2 t).const_mul β).div_const 2) using 1 <;> simp [fohAxisPhase] <;> ring

theorem fohAxisH_derivative (δ β t : ℝ) :
    HasDerivAt (fohAxisH δ β) (Complex.I*(δ+β*t)*fohAxisH δ β t) t := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (fohAxisPhase_derivative δ β t)
  have hh := (h.mul_const Complex.I).cexp
  convert hh using 1
  simp only [Function.comp_def, Complex.ofRealCLM_apply, fohAxisH, Complex.ofReal_add, Complex.ofReal_mul]
  ring

set_option maxHeartbeats 1000000 in
theorem fohAxisF1_derivative (F₀ : ℝ → ℂ) (δ β t : ℝ) (hβ : β ≠ 0)
    (hF : HasDerivAt F₀ (fohAxisH δ β t) t) :
    HasDerivAt (fohAxisF1 F₀ δ β) ((t:ℂ)*fohAxisH δ β t) t := by
  have hh := (((fohAxisH_derivative δ β t).sub_const 1).div_const (Complex.I*β)).sub
    (hF.const_mul ((δ:ℂ)/β))
  convert hh using 1
  field_simp [Complex.ofReal_ne_zero.mpr hβ]
  ring

set_option maxHeartbeats 1000000 in
theorem fohAxisF2_derivative (F₀ : ℝ → ℂ) (δ β t : ℝ) (hβ : β ≠ 0)
    (hF : HasDerivAt F₀ (fohAxisH δ β t) t) :
    HasDerivAt (fohAxisF2 F₀ δ β) ((t:ℂ)^2*fohAxisH δ β t) t := by
  have ht := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
  have hh := (((ht.mul (fohAxisH_derivative δ β t)).sub hF).div_const
    (Complex.I*β)).sub ((fohAxisF1_derivative F₀ δ β t hβ hF).const_mul ((δ:ℂ)/β))
  convert hh using 1
  simp only [Function.comp_def, Complex.ofRealCLM_apply, id_eq, Complex.ofReal_one]
  field_simp [Complex.ofReal_ne_zero.mpr hβ]
  ring

@[simp] theorem fohAxisF1_initial (F₀ : ℝ → ℂ) (δ β : ℝ) (h0 : F₀ 0 = 0) :
    fohAxisF1 F₀ δ β 0 = 0 := by simp [fohAxisF1, fohAxisH, fohAxisPhase, h0]

@[simp] theorem fohAxisF2_initial (F₀ : ℝ → ℂ) (δ β : ℝ) (h0 : F₀ 0 = 0) :
    fohAxisF2 F₀ δ β 0 = 0 := by simp [fohAxisF2, h0]

def fohAxisMoment (e : Vec3) (j : ℕ) (F : ℝ → ℂ) (t : ℝ) (x : Vec3) : Vec3 :=
  (t^(j+1)/(j+1)) • x + (F t).im • (skew e *ᵥ x) +
    (t^(j+1)/(j+1)-(F t).re) • (skew e^2 *ᵥ x)

/-- The same moment in the companion's parallel/perpendicular projector form. -/
theorem fohAxisMoment_projectors (e x : Vec3) (he : e ⬝ᵥ e = 1)
    (j : ℕ) (F : ℝ → ℂ) (t : ℝ) :
    fohAxisMoment e j F t x = (t^(j+1)/(j+1)) • ((e ⬝ᵥ x) • e) +
      (F t).re • (x-(e ⬝ᵥ x) • e) + (F t).im • (e ⨯₃ x) := by
  have hh : skew e^2 *ᵥ x = (e ⬝ᵥ x) • e-x := by
    rw [pow_two, ← Matrix.mulVec_mulVec, skew_mulVec, skew_mulVec,
      cross_cross_eq_smul_sub_smul', he, one_smul]
  rw [fohAxisMoment, hh, skew_mulVec]
  module

@[simp] theorem fohAxisMoment_initial (e : Vec3) (j : ℕ) (F : ℝ → ℂ)
    (h0 : F 0 = 0) : fohAxisMoment e j F 0 = fun _ => 0 := by
  funext x
  simp [fohAxisMoment, h0]

set_option maxHeartbeats 1000000 in
theorem fohAxisMoment_derivative (e : Vec3) (he : e ⬝ᵥ e = 1)
    (j : ℕ) (F : ℝ → ℂ) (θ t : ℝ) (x : Vec3)
    (hF : HasDerivAt F ((t:ℂ)^j*Complex.exp ((θ:ℂ)*Complex.I)) t) :
    HasDerivAt (fun u => fohAxisMoment e j F u x)
      (t^j • rotate (rotationExp (θ • e)) x) t := by
  have hRe : HasDerivAt (fun u => (F u).re) (t^j*cos θ) t := by
    simpa only [Function.comp_def, Complex.reCLM_apply, ← Complex.ofReal_pow,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hF
  have hIm : HasDerivAt (fun u => (F u).im) (t^j*sin θ) t := by
    simpa only [Function.comp_def, Complex.imCLM_apply, ← Complex.ofReal_pow,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.exp_ofReal_mul_I_im] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hF
  have hp : HasDerivAt (fun u : ℝ => u^(j+1)/((j:ℝ)+1)) (t^j) t := by
    convert (hasDerivAt_pow (j+1) t).div_const ((j:ℝ)+1) using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    field_simp
  have hh := ((hp.smul_const x).add (hIm.smul_const (skew e *ᵥ x))).add
    ((hp.sub hRe).smul_const (skew e^2 *ᵥ x))
  convert hh using 1
  have hcube := skew_cube e
  rw [enorm_sq, ← dot_self_lengthSq, he] at hcube
  have hr : (rotationExp (θ • e)).val = Preintegration.rodrigues (skew e) 1 θ := by
    simpa [rotationExp, skew_smul] using
      Preintegration.exp_rodrigues (skew e) 1 θ one_ne_zero (by simpa using hcube)
  rw [rotate, hr]
  simp only [Preintegration.rodrigues, Preintegration.f₁, one_mul, div_one, one_pow,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, smul_add, smul_smul]
  module

/-- Actual fixed-axis rotation reconstructed from the original time ODE. -/
theorem foh_fixed_axis_rotation (R : ℝ → SO3) (e : Vec3) (δ β : ℝ)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val)
      ((R t).val * skew ((δ+β*t) • e)) t) (hR0 : R 0 = 1) :
    R = fun t => rotationExp (fohAxisPhase δ β t • e) := by
  apply foh_rotation_ode_unique R _ (fun t => (δ+β*t) • e) hR
  · intro t
    exact foh_fixed_axis_derivative _ e (fohAxisPhase_derivative δ β t)
  · simpa [fohAxisPhase, foh_rotationExp_zero] using hR0

def fohAxisF (F₀ : ℝ → ℂ) (δ β : ℝ) : ℕ → ℝ → ℂ
  | 0 => F₀
  | 1 => fohAxisF1 F₀ δ β
  | _ => fohAxisF2 F₀ δ β

/-- Full fixed-axis endpoints from an actual zeroth oscillatory primitive.
The Gaussian module supplies that primitive from the normalized entire erf. -/
theorem foh_fixed_axis_endpoints_of_primitive
    (R : ℝ → SO3) (v p : ℝ → Vec3) (e a b : Vec3) (δ β : ℝ)
    (he : e ⬝ᵥ e = 1) (hβ : β ≠ 0) (F₀ : ℝ → ℂ)
    (hF : ∀ t, HasDerivAt F₀ (fohAxisH δ β t) t) (hF0 : F₀ 0 = 0)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val)
      ((R t).val * skew ((δ+β*t) • e)) t) (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a+t • b)) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0) (T : ℝ) :
    R T = rotationExp (fohAxisPhase δ β T • e) ∧
    v T = fohAxisMoment e 0 F₀ T a + fohAxisMoment e 1 (fohAxisF1 F₀ δ β) T b ∧
    p T = T • (fohAxisMoment e 0 F₀ T a + fohAxisMoment e 1 (fohAxisF1 F₀ δ β) T b) -
      fohAxisMoment e 1 (fohAxisF1 F₀ δ β) T a - fohAxisMoment e 2 (fohAxisF2 F₀ δ β) T b := by
  have hr := foh_fixed_axis_rotation R e δ β hR hR0
  refine ⟨congrFun hr T, ?_⟩
  apply foh_three_moment_endpoints R v p a b
    (fun j => fohAxisMoment e j (fohAxisF F₀ δ β j)) _ _ hv hv0 hp hp0 T
  · intro j hj t x
    rw [hr]
    apply fohAxisMoment_derivative e he
    interval_cases j
    · simpa [fohAxisF, fohAxisH] using hF t
    · simpa [fohAxisF, fohAxisH] using fohAxisF1_derivative F₀ δ β t hβ (hF t)
    · simpa [fohAxisF, fohAxisH] using fohAxisF2_derivative F₀ δ β t hβ (hF t)
  · intro j hj x
    interval_cases j <;> simp [fohAxisF, fohAxisMoment, hF0, fohAxisF1_initial, fohAxisF2_initial]

/-- Exact changing-rate fixed-axis FOH endpoints using the proved entire Gaussian
primitive, with no assumed oscillatory integral or parameter sensitivity. -/
theorem foh_fixed_axis_gaussian_endpoints
    (R : ℝ → SO3) (v p : ℝ → Vec3) (e a b : Vec3) (δ β : ℝ)
    (he : e ⬝ᵥ e = 1) (hβ : 0 < β)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val)
      ((R t).val * skew ((δ+β*t) • e)) t) (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a+t • b)) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0) (T : ℝ) :
    let F₀ := fohGaussianF0 δ β (fohGaussianRoot β)
    R T = rotationExp (fohAxisPhase δ β T • e) ∧
    v T = fohAxisMoment e 0 F₀ T a + fohAxisMoment e 1 (fohAxisF1 F₀ δ β) T b ∧
    p T = T • (fohAxisMoment e 0 F₀ T a + fohAxisMoment e 1 (fohAxisF1 F₀ δ β) T b) -
      fohAxisMoment e 1 (fohAxisF1 F₀ δ β) T a - fohAxisMoment e 2 (fohAxisF2 F₀ δ β) T b := by
  apply foh_fixed_axis_endpoints_of_primitive R v p e a b δ β he hβ.ne'
    (fohGaussianF0 δ β (fohGaussianRoot β)) _
    (foh_gaussianF0_initial δ β (fohGaussianRoot β)) hR hR0 hv hv0 hp hp0 T
  intro t
  convert foh_gaussianF0_hasDerivAt δ β (fohGaussianRoot β) hβ.ne'
    (foh_gaussianRoot_sq hβ.le) t using 1
  congr 1
  simp only [fohAxisH, fohAxisPhase, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  congr 1
  ring

theorem fohConstantF_derivative (δ : ℝ) (hδ : δ ≠ 0) (j : ℕ) (t : ℝ) :
    HasDerivAt (fohConstantF δ j)
      ((t:ℂ)^j*Complex.exp (((δ*t:ℝ):ℂ)*Complex.I)) t := by
  obtain ⟨hc, hs⟩ := fohTrigMoment_derivative δ hδ j t
  have hcc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hc
  have hss := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hs
  convert hcc.add (hss.mul_const Complex.I) using 1
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- The constant-rate branch in exactly the companion's complex-moment form. -/
theorem foh_constant_axis_endpoints
    (R : ℝ → SO3) (v p : ℝ → Vec3) (e a b : Vec3) (δ : ℝ)
    (he : e ⬝ᵥ e = 1) (hδ : δ ≠ 0)
    (hR : ∀ t, HasDerivAt (fun u => (R u).val)
      ((R t).val * skew (δ • e)) t) (hR0 : R 0 = 1)
    (hv : ∀ t, HasDerivAt v (rotate (R t) (a+t • b)) t) (hv0 : v 0 = 0)
    (hp : ∀ t, HasDerivAt p (v t) t) (hp0 : p 0 = 0) (T : ℝ) :
    R T = rotationExp ((δ*T) • e) ∧
    v T = fohAxisMoment e 0 (fohConstantF δ 0) T a + fohAxisMoment e 1 (fohConstantF δ 1) T b ∧
    p T = T • (fohAxisMoment e 0 (fohConstantF δ 0) T a +
      fohAxisMoment e 1 (fohConstantF δ 1) T b) -
      fohAxisMoment e 1 (fohConstantF δ 1) T a - fohAxisMoment e 2 (fohConstantF δ 2) T b := by
  have hr : R = fun t => rotationExp ((δ*t) • e) := by
    simpa only [fohAxisPhase, zero_mul, zero_div, add_zero] using
      foh_fixed_axis_rotation R e δ 0 (by simpa using hR) hR0
  refine ⟨congrFun hr T, ?_⟩
  apply foh_three_moment_endpoints R v p a b
    (fun j => fohAxisMoment e j (fohConstantF δ j)) _ _ hv hv0 hp hp0 T
  · intro j _ t x
    rw [hr]
    exact fohAxisMoment_derivative e he j _ (δ*t) t x (fohConstantF_derivative δ hδ j t)
  · intro j _ x
    simp [fohAxisMoment, fohConstantF, fohTrigMoment_initial]

end GNC.Magnus
