import GNC.Analysis.InitialPolynomialSupersolution
import GNC.Dynamics.PlanarCoastDefect

/-! One certified coast step of the planar Kepler integrator. A `Step`
packages a rational polynomial `Candidate` with the rational error radii of
the second-order envelope: the initial position and velocity radii `rp`,
`rv`, the tube radius `M`, and the certified terminal radii `rpEnd`,
`rvEnd`. The rational stiffness `kappa = 2/(rhoMin-M)^3` is the Lipschitz
constant of the inverse-square field on the tube; the normalized stiffness
`k = h^2 kappa` drives the explicit polynomial envelope of
`InitialPolynomialSupersolution`. The rational envelope values `envQ`,
`envVQ` are exact copies of that real envelope, so the terminal radii are
checked by rational arithmetic and transported to the real trajectory bound
through `step_envelope`. -/
noncomputable section
namespace GNC.CertifiedCoast
open Set GNC.PlanarCoast GNC.PlanarCoast.Candidate GNC.InitialPolynomialSupersolution

/-! ### Rational copies of the envelope polynomials -/

/-- Cosine-like polynomial `c` in exact rationals. -/
def cQ (k τ : ℚ) : ℚ := 1+k/2*τ^2+k^2/24*τ^4+k^3/720*τ^6+k^4/(720*(56-k))*τ^8
/-- Sine-like polynomial `s` in exact rationals. -/
def sQ (k τ : ℚ) : ℚ := τ+k/6*τ^3+k^2/120*τ^5+k^3/5040*τ^7+k^4/(5040*(72-k))*τ^9
/-- Unit-forcing supersolution `value` in exact rationals. -/
def hQ (k τ : ℚ) : ℚ := 1/2*τ^2+k/24*τ^4+k^2/720*τ^6+k^3/(720*(56-k))*τ^8
/-- Derivative `cv` of `c` in exact rationals. -/
def cvQ (k τ : ℚ) : ℚ := k*τ+k^2/6*τ^3+k^3/120*τ^5+k^4/(90*(56-k))*τ^7
/-- Derivative `sv` of `s` in exact rationals. -/
def svQ (k τ : ℚ) : ℚ := 1+k/2*τ^2+k^2/24*τ^4+k^3/720*τ^6+k^4/(560*(72-k))*τ^8
/-- Derivative `velocity` of `value` in exact rationals. -/
def hvQ (k τ : ℚ) : ℚ := τ+k/6*τ^3+k^2/120*τ^5+8*k^3/(720*(56-k))*τ^7

theorem cQ_cast (k τ : ℚ) : ((cQ k τ : ℚ):ℝ) = c (k:ℝ) (τ:ℝ) := by
  simp only [cQ, c]; push_cast; ring
theorem sQ_cast (k τ : ℚ) : ((sQ k τ : ℚ):ℝ) = s (k:ℝ) (τ:ℝ) := by
  simp only [sQ, s]; push_cast; ring
theorem hQ_cast (k τ : ℚ) : ((hQ k τ : ℚ):ℝ) = PolynomialSupersolution.value (k:ℝ) (τ:ℝ) := by
  simp only [hQ, PolynomialSupersolution.value, PolynomialSupersolution.polynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  push_cast; ring
theorem cvQ_cast (k τ : ℚ) : ((cvQ k τ : ℚ):ℝ) = cv (k:ℝ) (τ:ℝ) := by
  simp only [cvQ, cv]; push_cast; ring
theorem svQ_cast (k τ : ℚ) : ((svQ k τ : ℚ):ℝ) = sv (k:ℝ) (τ:ℝ) := by
  simp only [svQ, sv]; push_cast; ring
theorem hvQ_cast (k τ : ℚ) : ((hvQ k τ : ℚ):ℝ) = PolynomialSupersolution.velocity (k:ℝ) (τ:ℝ) := by
  simp only [hvQ, PolynomialSupersolution.velocity, PolynomialSupersolution.polynomial,
    Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one]
  push_cast; ring

/-! ### The certified step -/

/-- One certified coast step: a rational polynomial candidate together with
the rational error radii of its second-order envelope. -/
structure Step where
  c : Candidate
  /-- Initial position error radius (normalized length). -/
  rp : ℚ
  /-- Initial velocity error radius (normalized velocity). -/
  rv : ℚ
  /-- Tube radius; the field Lipschitz constant uses the floor `rhoMin-M`. -/
  M : ℚ
  /-- Certified terminal position error radius. -/
  rpEnd : ℚ
  /-- Certified terminal velocity error radius. -/
  rvEnd : ℚ

namespace Step

/-- Step length. -/
def h (s : Step) : ℚ := s.c.h
/-- Unscaled field Lipschitz constant on the tube of radius `M`. -/
def kappa (s : Step) : ℚ := 2/(s.c.rhoMin-s.M)^3
/-- Normalized stiffness `h^2 kappa`. -/
def k (s : Step) : ℚ := s.c.h^2*s.kappa

/-- Rational position envelope value. -/
def envQ (s : Step) (τ : ℚ) : ℚ :=
  s.rp*cQ s.k τ+(s.c.h*s.rv)*sQ s.k τ+(s.c.h^2*s.c.defect)*hQ s.k τ
/-- Rational velocity envelope value. -/
def envVQ (s : Step) (τ : ℚ) : ℚ :=
  s.rp*cvQ s.k τ+(s.c.h*s.rv)*svQ s.k τ+(s.c.h^2*s.c.defect)*hvQ s.k τ

/-- Real stiffness, matching `T^2 κ` of `step_envelope` with `T = h`. -/
def kR (s : Step) : ℝ := (s.c.h:ℝ)^2*(2/((s.c.rhoMin:ℝ)-(s.M:ℝ))^3)

theorem k_cast (s : Step) : ((s.k : ℚ):ℝ) = s.kR := by
  simp only [k, kappa, kR]; push_cast; ring

/-- Real position envelope, `envelope` at the real step data. -/
def envR (s : Step) (τ : ℝ) : ℝ :=
  envelope s.kR (s.rp:ℝ) ((s.c.h:ℝ)*(s.rv:ℝ)) ((s.c.h:ℝ)^2*(s.c.defect:ℝ)) τ
/-- Real velocity envelope. -/
def envVR (s : Step) (τ : ℝ) : ℝ :=
  envelopeVelocity s.kR (s.rp:ℝ) ((s.c.h:ℝ)*(s.rv:ℝ)) ((s.c.h:ℝ)^2*(s.c.defect:ℝ)) τ

theorem envQ_cast (s : Step) (τ : ℚ) : ((s.envQ τ : ℚ):ℝ) = s.envR (τ:ℝ) := by
  simp only [envQ, envR, envelope]
  push_cast [cQ_cast, sQ_cast, hQ_cast, k_cast]
  ring

theorem envVQ_cast (s : Step) (τ : ℚ) : ((s.envVQ τ : ℚ):ℝ) = s.envVR (τ:ℝ) := by
  simp only [envVQ, envVR, envelopeVelocity]
  push_cast [cvQ_cast, svQ_cast, hvQ_cast, k_cast]
  ring

/-- The decidable rational inequalities that certify the step. -/
def Valid (s : Step) : Prop :=
  s.c.Valid ∧ 0 < s.c.h ∧ 0 ≤ s.rp ∧ 0 ≤ s.rv ∧ s.M < s.c.rhoMin ∧
    s.k < 56 ∧ s.envQ 1 < s.M ∧ s.envQ 1 ≤ s.rpEnd ∧ s.envVQ 1/s.c.h ≤ s.rvEnd

instance (s : Step) : Decidable s.Valid := by unfold Valid; infer_instance

/-- Acceleration hypothesis with the tighter `defect` forcing (the kinematic
mismatch is charged to the velocity radius, not the acceleration). -/
theorem acceleration_hypothesis_defect (c : Candidate) (hv : c.Valid)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) {M : ℝ} (hM : M < c.rhoMin)
    (w : ℝ → Fin 4 → ℝ) (hp : ‖truePos w t-c.pos t‖ ≤ M) :
    ‖Gravity.field 1 (truePos w t)-c.acc t‖ ≤
      (2/((c.rhoMin:ℝ)-M)^3)*‖truePos w t-c.pos t‖+(c.defect:ℝ) := by
  have he : Gravity.field 1 (truePos w t)-c.acc t =
      (Gravity.field 1 (truePos w t)-Gravity.field 1 (c.pos t))+
        (Gravity.field 1 (c.pos t)-c.acc t) := by abel
  have hl := c.field_lipschitz hv ht hM (truePos w t) (c.pos t) hp
    (by rw [sub_self, norm_zero]; exact (norm_nonneg _).trans hp)
  have hd := c.defect_bound hv ht
  rw [norm_sub_rev] at hd
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hl hd)

theorem defect_nonneg (c : Candidate) (hv : c.Valid) : (0:ℝ) ≤ (c.defect:ℝ) :=
  (norm_nonneg _).trans (c.defect_bound hv (left_mem_Icc.mpr (by exact_mod_cast hv.1)))

theorem M_lt_rhoMin (s : Step) (hs : s.Valid) : (s.M:ℝ) < (s.c.rhoMin:ℝ) := by
  exact_mod_cast hs.2.2.2.2.1

theorem kR_lt_56 (s : Step) (hs : s.Valid) : s.kR < 56 := by
  have h2 : ((s.k:ℚ):ℝ) < 56 := by exact_mod_cast hs.2.2.2.2.2.1
  rw [k_cast] at h2; exact h2

/-- The certified terminal envelope value stays strictly inside the tube. -/
theorem close (s : Step) (hs : s.Valid) : s.envR 1 < (s.M:ℝ) := by
  have h2 : ((s.envQ 1:ℚ):ℝ) < (s.M:ℝ) := by exact_mod_cast hs.2.2.2.2.2.2.1
  rw [envQ_cast] at h2; simpa using h2

/-- The terminal position envelope value is at most the certified `rpEnd`. -/
theorem one_le_rpEnd (s : Step) (hs : s.Valid) : s.envR 1 ≤ (s.rpEnd:ℝ) := by
  have h2 : ((s.envQ 1:ℚ):ℝ) ≤ (s.rpEnd:ℝ) := by exact_mod_cast hs.2.2.2.2.2.2.2.1
  rw [envQ_cast] at h2; simpa using h2

/-- The terminal velocity envelope value is at most the certified `rvEnd`. -/
theorem one_le_rvEnd (s : Step) (hs : s.Valid) : s.envVR 1/(s.c.h:ℝ) ≤ (s.rvEnd:ℝ) := by
  have h2 : ((s.envVQ 1/s.c.h:ℚ):ℝ) ≤ (s.rvEnd:ℝ) := by exact_mod_cast hs.2.2.2.2.2.2.2.2
  push_cast at h2
  rw [envVQ_cast] at h2; simpa using h2

/-- Soundness of one certified step: every true inverse-square solution whose
initial error is inside the initial radii stays inside the envelope on the
whole step. -/
theorem step_sound (s : Step) (hs : s.Valid) (w : ℝ → Fin 4 → ℝ)
    (hwc : Continuous w)
    (hw : ∀ t ∈ Icc (0:ℝ) (s.c.h:ℝ), HasDerivAt w (PolynomialOrbit.physicalRate 0 (w t)) t)
    (hp0 : ‖truePos w 0-s.c.pos 0‖ ≤ (s.rp:ℝ))
    (hv0 : ‖trueVel w 0-s.c.dpos 0‖ ≤ (s.rv:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) (s.c.h:ℝ),
      ‖truePos w t-s.c.pos t‖ ≤ s.envR (t/(s.c.h:ℝ)) ∧
        ‖trueVel w t-s.c.dpos t‖ ≤ s.envVR (t/(s.c.h:ℝ))/(s.c.h:ℝ) := by
  obtain ⟨hcv, hh0, hrp, hrv, hMlt, hk56, hclose, _, _⟩ := hs
  have hMr : (s.M:ℝ) < (s.c.rhoMin:ℝ) := by exact_mod_cast hMlt
  have hh0r : (0:ℝ) < (s.c.h:ℝ) := by exact_mod_cast hh0
  have hden : (0:ℝ) < (s.c.rhoMin:ℝ)-(s.M:ℝ) := by linarith
  -- continuity of the true curves and the error curves
  have hcw0 : Continuous (fun t => w t 0) := (continuous_apply 0).comp hwc
  have hcw1 : Continuous (fun t => w t 1) := (continuous_apply 1).comp hwc
  have hcw2 : Continuous (fun t => w t 2) := (continuous_apply 2).comp hwc
  have hcw3 : Continuous (fun t => w t 3) := (continuous_apply 3).comp hwc
  have hcTP : Continuous (truePos w) := by
    have : Continuous (fun t => (![w t 0, w t 1] : Fin 2 → ℝ)) := by
      apply continuous_pi; intro i; fin_cases i <;> simpa
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.continuous).comp this
  have hcTV : Continuous (trueVel w) := by
    have : Continuous (fun t => (![w t 2, w t 3] : Fin 2 → ℝ)) := by
      apply continuous_pi; intro i; fin_cases i <;> simpa
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.continuous).comp this
  have hpc : Continuous (fun t => truePos w t-s.c.pos t) := hcTP.sub s.c.pos_continuous
  have hvc : Continuous (fun t => trueVel w t-s.c.dpos t) := hcTV.sub s.c.dpos_continuous
  -- real stiffness value and forcing nonnegativity
  have hFnn : (0:ℝ) ≤ (s.c.defect:ℝ) := defect_nonneg s.c hcv
  have hknn : (0:ℝ) ≤ (2/((s.c.rhoMin:ℝ)-(s.M:ℝ))^3) := by positivity
  have hk56r : (s.c.h:ℝ)^2*(2/((s.c.rhoMin:ℝ)-(s.M:ℝ))^3) < 56 := by
    have := s.k_cast
    have h2 : ((s.k:ℚ):ℝ) < 56 := by exact_mod_cast hk56
    rw [this, kR] at h2; exact h2
  have hcloser : envelope ((s.c.h:ℝ)^2*(2/((s.c.rhoMin:ℝ)-(s.M:ℝ))^3)) (s.rp:ℝ)
      ((s.c.h:ℝ)*(s.rv:ℝ)) ((s.c.h:ℝ)^2*(s.c.defect:ℝ)) 1 < (s.M:ℝ) := by
    have h2 : ((s.envQ 1:ℚ):ℝ) < (s.M:ℝ) := by exact_mod_cast hclose
    rw [envQ_cast, envR, kR] at h2; push_cast at h2; exact h2
  -- apply the one-step envelope
  have hmain := step_envelope (fun t => truePos w t-s.c.pos t)
    (fun t => trueVel w t-s.c.dpos t)
    (fun t => Gravity.field 1 (truePos w t)-s.c.acc t)
    (fun _ => (s.c.defect:ℝ))
    (T := (s.c.h:ℝ)) (κ := 2/((s.c.rhoMin:ℝ)-(s.M:ℝ))^3) (F := (s.c.defect:ℝ))
    (rp := (s.rp:ℝ)) (rv := (s.rv:ℝ)) (M := (s.M:ℝ))
    hh0r hknn hFnn hk56r hcloser hpc hvc
    (fun t _ => errorPos_hasDerivAt s.c (hw t (by assumption)))
    (fun t _ => errorVel_hasDerivAt s.c (hw t (by assumption)))
    hp0 hv0 (fun _ _ => le_rfl)
    (fun t ht hp => acceleration_hypothesis_defect s.c hcv ht hMr w hp)
  intro t ht
  have := hmain t ht
  rw [envR, envVR, kR]
  exact this

/-- The terminal position and velocity errors of one certified step are at
most the certified rational terminal radii. -/
theorem step_terminal (s : Step) (hs : s.Valid) (w : ℝ → Fin 4 → ℝ)
    (hwc : Continuous w)
    (hw : ∀ t ∈ Icc (0:ℝ) (s.c.h:ℝ), HasDerivAt w (PolynomialOrbit.physicalRate 0 (w t)) t)
    (hp0 : ‖truePos w 0-s.c.pos 0‖ ≤ (s.rp:ℝ))
    (hv0 : ‖trueVel w 0-s.c.dpos 0‖ ≤ (s.rv:ℝ)) :
    ‖truePos w (s.c.h:ℝ)-s.c.pos (s.c.h:ℝ)‖ ≤ (s.rpEnd:ℝ) ∧
      ‖trueVel w (s.c.h:ℝ)-s.c.dpos (s.c.h:ℝ)‖ ≤ (s.rvEnd:ℝ) := by
  have hh0 : (0:ℝ) < (s.c.h:ℝ) := by exact_mod_cast hs.2.1
  obtain ⟨hp, hv⟩ := step_sound s hs w hwc hw hp0 hv0 (s.c.h:ℝ)
    ⟨hh0.le, le_rfl⟩
  rw [div_self hh0.ne'] at hp hv
  have hpE : s.envR 1 = ((s.envQ 1:ℚ):ℝ) := by
    have := (envQ_cast s 1).symm; simpa using this
  have hvE : s.envVR 1 = ((s.envVQ 1:ℚ):ℝ) := by
    have := (envVQ_cast s 1).symm; simpa using this
  constructor
  · rw [hpE] at hp
    exact hp.trans (by exact_mod_cast hs.2.2.2.2.2.2.2.1)
  · rw [hvE] at hv
    have hvend : ((s.envVQ 1:ℚ):ℝ)/(s.c.h:ℝ) ≤ (s.rvEnd:ℝ) := by
      have : ((s.envVQ 1/s.c.h : ℚ):ℝ) ≤ (s.rvEnd:ℝ) := by exact_mod_cast hs.2.2.2.2.2.2.2.2
      push_cast at this; exact this
    exact hv.trans hvend

end Step
end GNC.CertifiedCoast
