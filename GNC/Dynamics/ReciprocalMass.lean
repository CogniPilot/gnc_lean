import GNC.Dynamics.VariableMassThrust
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Field.GeomSum

/-! Reciprocal mass, its polynomial truncation, and the flat-space closed forms
for a constant-force burn under linear mass depletion.

The instantaneous mass is `mass m₀ σ t = m₀ - σ t`; the reciprocal mass
`recip m₀ σ t = 1 / mass m₀ σ t` is the state that enters a force-commanded
acceleration `F w`. The geometric truncation `wK` is a polynomial candidate for
`recip`, and its tail is controlled by the depletion ratio `ρ = σ T / m₀`. The
scalar velocity and displacement gained during the burn are the logarithmic
closed forms `scalarDeltaV` and `scalarDeltaP`, proved here as solutions of the
governing differential equations. The planar burn from a fixed inertial
attitude is written on the complex line, where the rotation by a misalignment
angle `δ` is multiplication by `exp (δ i)`; the chord and second-order estimates
of the misalignment displacement are the trigonometric bounds
`‖R δ e - e‖ = 2 |sin (δ/2)| ≤ |δ|` and `‖R δ e - e - δ (J e)‖ ≤ δ²/2 + |δ|³/6`. -/
noncomputable section
namespace GNC.ReciprocalMass
open Real MeasureTheory intervalIntegral

/-! ### Mass, reciprocal mass, and their derivatives -/

/-- Linearly depleting mass with initial value `m₀` and mass rate `σ`. -/
def mass (m₀ σ t : ℝ) : ℝ := m₀ - σ * t

/-- Reciprocal mass, the state entering a force-commanded acceleration. -/
def recip (m₀ σ t : ℝ) : ℝ := (mass m₀ σ t)⁻¹

theorem mass_hasDerivAt (m₀ σ t : ℝ) : HasDerivAt (mass m₀ σ) (-σ) t := by
  simpa [mass] using (hasDerivAt_const t m₀).sub ((hasDerivAt_id t).const_mul σ)

/-- Remaining mass is positive throughout `[0, T]` when the depleted fraction
`σ T` stays below the initial mass. -/
theorem mass_pos {m₀ σ T t : ℝ} (hσ : 0 ≤ σ) (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hT : σ * T < m₀) : 0 < mass m₀ σ t := by
  have : σ * t ≤ σ * T := mul_le_mul_of_nonneg_left htT hσ
  simp only [mass]; linarith

/-- Reciprocal mass solves `ẇ = σ w²` while the mass is nonzero (equation
`ẇ = s w²` of the design brief). -/
theorem recip_hasDerivAt {m₀ σ t : ℝ} (hpos : 0 < mass m₀ σ t) :
    HasDerivAt (recip m₀ σ) (σ * (recip m₀ σ t) ^ 2) t :=
  VariableMassThrust.inverse_mass_derivative (mass_hasDerivAt m₀ σ t) hpos

theorem recip_pos {m₀ σ t : ℝ} (hpos : 0 < mass m₀ σ t) : 0 < recip m₀ σ t :=
  inv_pos.mpr hpos

/-! ### General candidate identity

A polynomial (or any) candidate `ŵ` is certified against the true reciprocal
mass by the residual of `ŵ · m - 1`. -/

/-- Exact residual of a reciprocal-mass candidate `ŵ`. -/
theorem candidate_error_eq {m₀ σ t : ℝ} (ŵ : ℝ) (hm : mass m₀ σ t ≠ 0) :
    recip m₀ σ t - ŵ = (1 - ŵ * mass m₀ σ t) / mass m₀ σ t := by
  rw [recip]; field_simp

/-- The candidate error is controlled by `|ŵ · m - 1| / m`: a polynomial
candidate `ŵ` is certified by the polynomial `ŵ · m - 1`. -/
theorem candidate_error_abs {m₀ σ t : ℝ} (ŵ : ℝ) (hpos : 0 < mass m₀ σ t) :
    |recip m₀ σ t - ŵ| ≤ |ŵ * mass m₀ σ t - 1| / mass m₀ σ t := by
  rw [candidate_error_eq ŵ hpos.ne', abs_div, abs_of_pos hpos, abs_sub_comm]

/-! ### Geometric truncation and its tail bound -/

/-- The degree-`K` geometric truncation of reciprocal mass:
`wK = (1/m₀) Σ_{k ≤ K} (σ t / m₀)^k`. -/
def wK (m₀ σ : ℝ) (K : ℕ) (t : ℝ) : ℝ :=
  m₀⁻¹ * ∑ k ∈ Finset.range (K + 1), (σ * t / m₀) ^ k

/-- The exact residual of the geometric truncation as a single tail term,
`recip - wK = x^{K+1}/(m₀(1-x))` with `x = σ t / m₀`. -/
theorem recip_sub_wK {m₀ σ t : ℝ} (K : ℕ) (hm₀ : 0 < m₀) (hx : σ * t / m₀ ≠ 1) :
    recip m₀ σ t - wK m₀ σ K t =
      (σ * t / m₀) ^ (K + 1) / (m₀ * (1 - σ * t / m₀)) := by
  have hm0 : m₀ ≠ 0 := hm₀.ne'
  set x := σ * t / m₀ with hxdef
  have hone : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hmass : mass m₀ σ t = m₀ * (1 - x) := by
    rw [hxdef, mass]; field_simp
  rw [recip, wK, hmass, geom_sum_eq hx]
  field_simp
  ring

/-- Tail bound: for `t ∈ [0, T]` with depletion ratio `ρ = σ T / m₀ < 1`, the
geometric truncation error is at most `ρ^{K+1} / (m₀ (1 - ρ))`. -/
theorem wK_tail_bound {m₀ σ T t : ℝ} (K : ℕ) (hm₀ : 0 < m₀) (hσ : 0 ≤ σ)
    (ht0 : 0 ≤ t) (htT : t ≤ T) (hρ : σ * T / m₀ < 1) :
    |recip m₀ σ t - wK m₀ σ K t| ≤
      (σ * T / m₀) ^ (K + 1) / (m₀ * (1 - σ * T / m₀)) := by
  have hx0 : 0 ≤ σ * t / m₀ := div_nonneg (mul_nonneg hσ ht0) hm₀.le
  have hxρ : σ * t / m₀ ≤ σ * T / m₀ := by gcongr
  have hxlt : σ * t / m₀ < 1 := lt_of_le_of_lt hxρ hρ
  have hone : (0 : ℝ) < 1 - σ * t / m₀ := by linarith
  have honeρ : (0 : ℝ) < 1 - σ * T / m₀ := by linarith
  have hanum : (0 : ℝ) ≤ (σ * t / m₀) ^ (K + 1) := pow_nonneg hx0 _
  have hcnum : (0 : ℝ) ≤ (σ * T / m₀) ^ (K + 1) := pow_nonneg (le_trans hx0 hxρ) _
  have hb : (0 : ℝ) < m₀ * (1 - σ * t / m₀) := mul_pos hm₀ hone
  have hd : (0 : ℝ) < m₀ * (1 - σ * T / m₀) := mul_pos hm₀ honeρ
  rw [recip_sub_wK K hm₀ hxlt.ne, abs_of_nonneg (div_nonneg hanum hb.le)]
  exact div_le_div₀ hcnum (pow_le_pow_left₀ hx0 hxρ _) hd (by gcongr)

/-! ### Scalar closed forms for the burn

The scalar velocity and displacement gained by a constant force `F` under linear
mass depletion, expressed through the logarithm of the mass ratio. -/

/-- Scalar velocity increment `Δv(t) = (F/σ) log(m₀ / m(t))`. -/
def scalarDeltaV (F m₀ σ t : ℝ) : ℝ := (F / σ) * Real.log (m₀ / mass m₀ σ t)

/-- Scalar displacement increment
`Δp(t) = (F/σ) (t - (m(t)/σ) log(m₀ / m(t)))`. -/
def scalarDeltaP (F m₀ σ t : ℝ) : ℝ :=
  (F / σ) * (t - (mass m₀ σ t / σ) * Real.log (m₀ / mass m₀ σ t))

/-- Derivative of the mass-ratio logarithm: `d/dt log(m₀/m) = σ w`. -/
theorem logMassRatio_hasDerivAt {m₀ σ t : ℝ} (hm₀ : 0 < m₀) (hpos : 0 < mass m₀ σ t) :
    HasDerivAt (fun s => Real.log (m₀ / mass m₀ σ s)) (σ * recip m₀ σ t) t := by
  have hfun : (fun s => Real.log (m₀ / mass m₀ σ s))
      = fun s => Real.log (m₀ * recip m₀ σ s) := by
    funext s; rw [recip, div_eq_mul_inv]
  rw [hfun]
  have h1 : HasDerivAt (fun s => m₀ * recip m₀ σ s) (m₀ * (σ * (recip m₀ σ t) ^ 2)) t :=
    (recip_hasDerivAt hpos).const_mul m₀
  have hne : m₀ * recip m₀ σ t ≠ 0 := by
    have := recip_pos hpos; positivity
  have h2 := h1.log hne
  convert h2 using 1
  rw [recip]
  field_simp

/-- The scalar velocity closed form solves `Δv' = F w`. -/
theorem scalarDeltaV_hasDerivAt {F m₀ σ t : ℝ} (hm₀ : 0 < m₀) (hσ : σ ≠ 0)
    (hpos : 0 < mass m₀ σ t) :
    HasDerivAt (scalarDeltaV F m₀ σ) (F * recip m₀ σ t) t := by
  have h : HasDerivAt (scalarDeltaV F m₀ σ) ((F / σ) * (σ * recip m₀ σ t)) t :=
    (logMassRatio_hasDerivAt hm₀ hpos).const_mul (F / σ)
  rwa [show (F / σ) * (σ * recip m₀ σ t) = F * recip m₀ σ t by field_simp] at h

/-- The scalar displacement closed form solves `Δp' = Δv`. -/
theorem scalarDeltaP_hasDerivAt {F m₀ σ t : ℝ} (hm₀ : 0 < m₀) (hσ : σ ≠ 0)
    (hpos : 0 < mass m₀ σ t) :
    HasDerivAt (scalarDeltaP F m₀ σ) (scalarDeltaV F m₀ σ t) t := by
  have hL := logMassRatio_hasDerivAt hm₀ hpos
  have hM := mass_hasDerivAt m₀ σ t
  have hg : HasDerivAt (fun s => mass m₀ σ s / σ * Real.log (m₀ / mass m₀ σ s))
      (-Real.log (m₀ / mass m₀ σ t) + 1) t := by
    have hprod := (hM.div_const σ).mul hL
    convert hprod using 1
    rw [recip]
    field_simp
  have hP : HasDerivAt (scalarDeltaP F m₀ σ)
      ((F / σ) * (1 - (-Real.log (m₀ / mass m₀ σ t) + 1))) t :=
    ((hasDerivAt_id t).sub hg).const_mul (F / σ)
  rwa [show (F / σ) * (1 - (-Real.log (m₀ / mass m₀ σ t) + 1))
      = scalarDeltaV F m₀ σ t by rw [scalarDeltaV]; ring] at hP

/-- Both scalar increments vanish at ignition. -/
@[simp] theorem scalarDeltaV_zero (F m₀ σ : ℝ) : scalarDeltaV F m₀ σ 0 = 0 := by
  by_cases h : m₀ = 0 <;> simp [scalarDeltaV, mass, h]

@[simp] theorem scalarDeltaP_zero (F m₀ σ : ℝ) : scalarDeltaP F m₀ σ 0 = 0 := by
  by_cases h : m₀ = 0 <;> simp [scalarDeltaP, mass, h]

/-! ### Integral form and truncation error of the impulse -/

theorem recip_continuousOn {m₀ σ T : ℝ} (hσ : 0 ≤ σ) (hm₀ : 0 < m₀)
    (hT : σ * T < m₀) (hTpos : 0 ≤ T) :
    ContinuousOn (recip m₀ σ) (Set.Icc 0 T) := by
  apply ContinuousOn.inv₀
  · exact (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  · intro t ht
    exact (mass_pos hσ ht.1 ht.2 hT).ne'

/-- The impulse `∫₀ᵀ F w` equals the logarithmic closed form `Δv(T)`. -/
theorem integral_recip {F m₀ σ T : ℝ} (hσ : 0 < σ) (hm₀ : 0 < m₀)
    (hT : σ * T < m₀) (hTpos : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, F * recip m₀ σ t) = scalarDeltaV F m₀ σ T := by
  have hcont : ContinuousOn (fun t => F * recip m₀ σ t) (Set.Icc 0 T) :=
    continuousOn_const.mul (recip_continuousOn hσ.le hm₀ hT hTpos)
  have hint : IntervalIntegrable (fun t => F * recip m₀ σ t) volume 0 T :=
    hcont.intervalIntegrable_of_Icc hTpos
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (scalarDeltaV F m₀ σ) (F * recip m₀ σ t) t := by
    intro t ht
    rw [Set.uIcc_of_le hTpos] at ht
    exact scalarDeltaV_hasDerivAt hm₀ hσ.ne' (mass_pos hσ.le ht.1 ht.2 hT)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  simp [scalarDeltaV, mass]

/-- The displacement is the integral of the velocity increment,
`∫₀ᵀ Δv = Δp(T)`. -/
theorem integral_scalarDeltaV {F m₀ σ T : ℝ} (hσ : 0 < σ) (hm₀ : 0 < m₀)
    (hT : σ * T < m₀) (hTpos : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, scalarDeltaV F m₀ σ t) = scalarDeltaP F m₀ σ T := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (scalarDeltaP F m₀ σ) (scalarDeltaV F m₀ σ t) t := by
    intro t ht
    rw [Set.uIcc_of_le hTpos] at ht
    exact scalarDeltaP_hasDerivAt hm₀ hσ.ne' (mass_pos hσ.le ht.1 ht.2 hT)
  have hcont : ContinuousOn (scalarDeltaV F m₀ σ) (Set.uIcc 0 T) := by
    intro t ht
    rw [Set.uIcc_of_le hTpos] at ht
    exact (scalarDeltaV_hasDerivAt hm₀ hσ.ne'
      (mass_pos hσ.le ht.1 ht.2 hT)).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
    scalarDeltaP_zero, sub_zero]

/-- The double impulse integral equals the displacement closed form,
`∫₀ᵀ ∫₀ᵗ F w = Δp(T)`. -/
theorem double_integral_recip {F m₀ σ T : ℝ} (hσ : 0 < σ) (hm₀ : 0 < m₀)
    (hT : σ * T < m₀) (hTpos : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ∫ s in (0 : ℝ)..t, F * recip m₀ σ s) = scalarDeltaP F m₀ σ T := by
  rw [← integral_scalarDeltaV hσ hm₀ hT hTpos]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hTpos] at ht
  exact integral_recip hσ hm₀ (lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 hσ.le) hT) ht.1

/-- Single-integral truncation error: replacing `w` by its degree-`K`
truncation changes the impulse integral over `[0, T]` by at most `|F| τ_K T`,
where `τ_K = ρ^{K+1}/(m₀(1-ρ))`. -/
theorem impulse_truncation_error {F m₀ σ T : ℝ} (K : ℕ) (hm₀ : 0 < m₀) (hσ : 0 ≤ σ)
    (hT : σ * T < m₀) (hTpos : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, (F * recip m₀ σ t - F * wK m₀ σ K t)‖ ≤
      |F| * ((σ * T / m₀) ^ (K + 1) / (m₀ * (1 - σ * T / m₀))) * T := by
  have hρ : σ * T / m₀ < 1 := (div_lt_one hm₀).mpr hT
  set τ := (σ * T / m₀) ^ (K + 1) / (m₀ * (1 - σ * T / m₀)) with hτ
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) T,
      ‖F * recip m₀ σ t - F * wK m₀ σ K t‖ ≤ |F| * τ := by
    intro t ht
    rw [Set.uIoc_of_le hTpos] at ht
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (wK_tail_bound K hm₀ hσ (le_of_lt ht.1) ht.2 hρ) (abs_nonneg F)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rwa [sub_zero, abs_of_nonneg hTpos] at h

/-- Double-integral truncation error: the displacement, obtained by integrating
the impulse a second time, changes by at most `|F| τ_K T²/2` under the degree-`K`
truncation. -/
theorem displacement_truncation_error {F m₀ σ T : ℝ} (K : ℕ) (hm₀ : 0 < m₀) (hσ : 0 ≤ σ)
    (hT : σ * T < m₀) (hTpos : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, ∫ s in (0 : ℝ)..t, (F * recip m₀ σ s - F * wK m₀ σ K s)‖ ≤
      |F| * ((σ * T / m₀) ^ (K + 1) / (m₀ * (1 - σ * T / m₀))) * T ^ 2 / 2 := by
  have hρ : σ * T / m₀ < 1 := (div_lt_one hm₀).mpr hT
  set τ := (σ * T / m₀) ^ (K + 1) / (m₀ * (1 - σ * T / m₀)) with hτ
  have hρ0 : 0 ≤ σ * T / m₀ := div_nonneg (mul_nonneg hσ hTpos) hm₀.le
  have h1ρ : 0 < 1 - σ * T / m₀ := by linarith
  have hinner : ∀ t, 0 ≤ t → t ≤ T →
      ‖∫ s in (0 : ℝ)..t, (F * recip m₀ σ s - F * wK m₀ σ K s)‖ ≤ |F| * τ * t := by
    intro t ht0 htT
    have hb : ∀ s ∈ Set.uIoc (0 : ℝ) t,
        ‖F * recip m₀ σ s - F * wK m₀ σ K s‖ ≤ |F| * τ := by
      intro s hs
      rw [Set.uIoc_of_le ht0] at hs
      rw [← mul_sub, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (wK_tail_bound K hm₀ hσ (le_of_lt hs.1) (hs.2.trans htT) hρ) (abs_nonneg F)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rwa [sub_zero, abs_of_nonneg ht0] at h
  have hae : ∀ᵐ t, t ∈ Set.Ioc (0 : ℝ) T →
      ‖∫ s in (0 : ℝ)..t, (F * recip m₀ σ s - F * wK m₀ σ K s)‖ ≤ |F| * τ * t :=
    Filter.Eventually.of_forall (fun t ht => hinner t (le_of_lt ht.1) ht.2)
  have hg : IntervalIntegrable (fun t => |F| * τ * t) volume 0 T :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 T
  have h := intervalIntegral.norm_integral_le_of_norm_le hTpos hae hg
  have hval : (∫ t in (0 : ℝ)..T, |F| * τ * t) = |F| * τ * T ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rwa [hval] at h

/-! ### Planar burn on the complex line

The plane is modelled by `ℂ`; a unit thrust direction is a complex number of
unit modulus, misalignment by `δ` is multiplication by `rot δ = exp (δ i)`, and
the transverse direction operator is `J e = i e`. -/

/-- Planar rotation as multiplication by `exp (δ i)` on the complex line. -/
def rot (δ : ℝ) : ℂ := Complex.exp (δ * Complex.I)

@[simp] theorem norm_rot (δ : ℝ) : ‖rot δ‖ = 1 := by
  rw [rot, Complex.norm_exp_ofReal_mul_I]

/-! #### Global trigonometric second-order bounds -/

/-- The quadratic upper bound `1 - cos δ ≤ δ²/2`, valid for every `δ`. -/
theorem one_sub_cos_le (δ : ℝ) : 1 - Real.cos δ ≤ δ ^ 2 / 2 := by
  have hcos : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 := by
    have := Real.cos_two_mul_eq_one_sub (δ / 2)
    rwa [mul_div_cancel₀ δ (two_ne_zero)] at this
  have hsin : Real.sin (δ / 2) ^ 2 ≤ (δ / 2) ^ 2 := by
    have h := Real.abs_sin_le_abs (x := δ / 2)
    nlinarith [abs_nonneg (Real.sin (δ / 2)), abs_nonneg (δ / 2), sq_abs (Real.sin (δ / 2)),
      sq_abs (δ / 2)]
  rw [hcos]
  nlinarith [hsin]

/-- The cubic bound `|δ - sin δ| ≤ |δ|³/6`, valid for every `δ`, obtained by
integrating the quadratic cosine bound. -/
theorem abs_sub_sin_le (δ : ℝ) : |δ - Real.sin δ| ≤ |δ| ^ 3 / 6 := by
  -- `f x = x³/6 - x + sin x` is monotone since `f' x = x²/2 - (1 - cos x) ≥ 0`
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => x ^ 3 / 6 - x + Real.sin x)
      (x ^ 2 / 2 - 1 + Real.cos x) x := by
    intro x
    have h := (((hasDerivAt_pow 3 x).div_const 6).sub (hasDerivAt_id x)).add
      (Real.hasDerivAt_sin x)
    convert h using 1
    push_cast; ring
  have hmono : Monotone (fun x => x ^ 3 / 6 - x + Real.sin x) := by
    apply monotone_of_deriv_nonneg
    · exact fun x => (hderiv x).differentiableAt
    · intro x
      rw [(hderiv x).deriv]
      have := one_sub_cos_le x
      linarith
  have key : ∀ x : ℝ, 0 ≤ x → x - Real.sin x ≤ x ^ 3 / 6 := by
    intro x hx
    have h := hmono hx
    simp only [Real.sin_zero] at h
    nlinarith [h]
  rcases le_total 0 δ with hδ | hδ
  · rw [abs_of_nonneg hδ, abs_of_nonneg (by linarith [Real.sin_le hδ] : 0 ≤ δ - Real.sin δ)]
    exact key δ hδ
  · have hneg : 0 ≤ -δ := by linarith
    have hd : δ - Real.sin δ ≤ 0 := by linarith [Real.le_sin hδ]
    rw [abs_of_nonpos hd, abs_of_nonpos hδ]
    have h := key (-δ) hneg
    rw [Real.sin_neg] at h
    linarith [h]

/-! #### Chord and second-order displacement bounds -/

/-- The rotation defect on the complex line: `rot δ - 1 = (cos δ - 1) + (sin δ) i`. -/
theorem rot_sub_one (δ : ℝ) :
    rot δ - 1 = (Real.cos δ - 1 : ℝ) + (Real.sin δ : ℝ) * Complex.I := by
  rw [rot, Complex.exp_ofReal_mul_I]
  push_cast; ring

/-- Chord length identity: `‖rot δ - 1‖ = 2 |sin (δ/2)|`. -/
theorem norm_rot_sub_one (δ : ℝ) : ‖rot δ - 1‖ = 2 * |Real.sin (δ / 2)| := by
  rw [rot_sub_one, Complex.norm_add_mul_I]
  have hcos : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 := by
    have := Real.cos_two_mul_eq_one_sub (δ / 2)
    rwa [mul_div_cancel₀ δ (two_ne_zero)] at this
  have hval : (Real.cos δ - 1) ^ 2 + Real.sin δ ^ 2 = (2 * |Real.sin (δ / 2)|) ^ 2 := by
    rw [mul_pow, sq_abs]
    have hpyth : Real.sin δ ^ 2 = 1 - Real.cos δ ^ 2 := by
      have := Real.sin_sq_add_cos_sq δ; nlinarith
    rw [hpyth, hcos]; ring
  rw [hval, Real.sqrt_sq (by positivity)]

/-- The chord defect of a unit direction: `‖rot δ e - e‖ = 2 |sin (δ/2)|`. -/
theorem norm_rot_smul_sub {e : ℂ} (he : ‖e‖ = 1) (δ : ℝ) :
    ‖rot δ * e - e‖ = 2 * |Real.sin (δ / 2)| := by
  rw [show rot δ * e - e = (rot δ - 1) * e by ring, norm_mul, he, mul_one, norm_rot_sub_one]

/-- Chord bound: `‖rot δ e - e‖ ≤ |δ|`. -/
theorem norm_rot_smul_sub_le {e : ℂ} (he : ‖e‖ = 1) (δ : ℝ) :
    ‖rot δ * e - e‖ ≤ |δ| := by
  rw [norm_rot_smul_sub he]
  have h := Real.abs_sin_le_abs (x := δ / 2)
  rw [abs_div] at h
  simp only [abs_two] at h
  linarith [h]

/-- Second-order misalignment bound with the transverse operator `J e = i e`:
`‖rot δ e - e - δ (i e)‖ ≤ δ²/2 + |δ|³/6`. -/
theorem norm_rot_smul_second_order {e : ℂ} (he : ‖e‖ = 1) (δ : ℝ) :
    ‖rot δ * e - e - (δ : ℂ) * (Complex.I * e)‖ ≤ δ ^ 2 / 2 + |δ| ^ 3 / 6 := by
  have hfac : rot δ * e - e - (δ : ℂ) * (Complex.I * e)
      = ((Real.cos δ - 1 : ℝ) + (Real.sin δ - δ : ℝ) * Complex.I) * e := by
    rw [rot, Complex.exp_ofReal_mul_I]; push_cast; ring
  rw [hfac, norm_mul, he, mul_one, Complex.norm_add_mul_I]
  have hb : Real.sqrt ((Real.cos δ - 1) ^ 2 + (Real.sin δ - δ) ^ 2)
      ≤ |Real.cos δ - 1| + |Real.sin δ - δ| := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ |Real.cos δ - 1| + |Real.sin δ - δ|)]
    apply Real.sqrt_le_sqrt
    nlinarith [abs_nonneg (Real.cos δ - 1), abs_nonneg (Real.sin δ - δ),
      sq_abs (Real.cos δ - 1), sq_abs (Real.sin δ - δ),
      mul_nonneg (abs_nonneg (Real.cos δ - 1)) (abs_nonneg (Real.sin δ - δ))]
  refine hb.trans ?_
  have h1 : |Real.cos δ - 1| ≤ δ ^ 2 / 2 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.cos_le_one δ] : (0:ℝ) ≤ 1 - Real.cos δ)]
    exact one_sub_cos_le δ
  have h2 : |Real.sin δ - δ| ≤ |δ| ^ 3 / 6 := by
    rw [abs_sub_comm]; exact abs_sub_sin_le δ
  linarith

/-! ### Flat-space burn as an ODE solution

For a constant misalignment `δ` and a unit thrust direction `e`, the planar
motion from `(q₀, v₀)` under acceleration `F w(t) (rot δ) e` is given in closed
form by the scalar increments applied along the (fixed) rotated direction. -/

/-- Closed-form velocity of the flat burn. -/
def burnVel (q0 v0 e : ℂ) (F m₀ σ δ : ℝ) (t : ℝ) : ℂ :=
  v0 + (scalarDeltaV F m₀ σ t : ℂ) * (rot δ * e)

/-- Closed-form position of the flat burn. -/
def burnPos (q0 v0 e : ℂ) (F m₀ σ δ : ℝ) (t : ℝ) : ℂ :=
  q0 + (t : ℂ) * v0 + (scalarDeltaP F m₀ σ t : ℂ) * (rot δ * e)

/-- The closed form starts from the given state `(q₀, v₀)`. -/
@[simp] theorem burnPos_zero (q0 v0 e : ℂ) (F m₀ σ δ : ℝ) :
    burnPos q0 v0 e F m₀ σ δ 0 = q0 := by
  simp [burnPos]

@[simp] theorem burnVel_zero (q0 v0 e : ℂ) (F m₀ σ δ : ℝ) :
    burnVel q0 v0 e F m₀ σ δ 0 = v0 := by
  simp [burnVel]

/-- The closed-form position differentiates to the closed-form velocity. -/
theorem burnPos_hasDerivAt {q0 v0 e : ℂ} {F m₀ σ δ : ℝ} {t : ℝ} (hm₀ : 0 < m₀)
    (hσ : σ ≠ 0) (hpos : 0 < mass m₀ σ t) :
    HasDerivAt (fun s => burnPos q0 v0 e F m₀ σ δ s) (burnVel q0 v0 e F m₀ σ δ t) t := by
  have hP := (scalarDeltaP_hasDerivAt (F := F) hm₀ hσ hpos).ofReal_comp
  have ht : HasDerivAt (fun s : ℝ => (s : ℂ) * v0) v0 t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).mul_const v0
  have h := (((hasDerivAt_const t q0).add ht).add (hP.mul_const (rot δ * e)))
  simpa [burnPos, burnVel] using h

/-- The closed-form velocity differentiates to the commanded acceleration
`F w(t) (rot δ) e`. -/
theorem burnVel_hasDerivAt {q0 v0 e : ℂ} {F m₀ σ δ : ℝ} {t : ℝ} (hm₀ : 0 < m₀)
    (hσ : σ ≠ 0) (hpos : 0 < mass m₀ σ t) :
    HasDerivAt (fun s => burnVel q0 v0 e F m₀ σ δ s)
      ((F * recip m₀ σ t : ℂ) * (rot δ * e)) t := by
  have hV := (scalarDeltaV_hasDerivAt (F := F) hm₀ hσ hpos).ofReal_comp
  have h : HasDerivAt (fun s => burnVel q0 v0 e F m₀ σ δ s)
      (0 + ↑(F * recip m₀ σ t) * (rot δ * e)) t :=
    (hasDerivAt_const t v0).add (hV.mul_const (rot δ * e))
  rw [zero_add, Complex.ofReal_mul] at h
  exact h

end GNC.ReciprocalMass
