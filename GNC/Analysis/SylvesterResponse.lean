import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
Response to an autonomous linear input generator, with all numerical defects
retained. The Sylvester equation is classical: this module supplies a checked
interface for using it inside a physical trajectory certificate. It does not
assert that a particular Sylvester solver or matrix exponential is exact.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.SylvesterResponse

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

abbrev End (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E

/-- The sign convention is `A S - S H = B`. -/
def residual (A : End V) (H : End W) (B S : W →L[ℝ] V) : W →L[ℝ] V :=
  A.comp S - S.comp H - B

/-- The zero-initial-data response operator when the Sylvester equation and
the two diagonal flow equations hold exactly. -/
def response (F : ℝ → End V) (Q : ℝ → End W) (S : W →L[ℝ] V)
    (t : ℝ) : W →L[ℝ] V := (F t).comp S - S.comp (Q t)

theorem response_zero (F : ℝ → End V) (Q : ℝ → End W) (S : W →L[ℝ] V)
    (hF : F 0 = 1) (hQ : Q 0 = 1) : response F Q S 0 = 0 := by
  ext w
  simp [response, hF, hQ]

/-- Even approximate diagonal flows and an approximate Sylvester solution
have an exact, explicitly computable differential defect. -/
theorem derivative_with_defects
    (A : End V) (H : End W) (B S : W →L[ℝ] V)
    (F : ℝ → End V) (Q : ℝ → End W) (EF : End V) (EQ : End W) (t : ℝ)
    (hF : HasDerivAt F (A.comp (F t) + EF) t)
    (hQ : HasDerivAt Q (H.comp (Q t) + EQ) t) :
    HasDerivAt (response F Q S)
      (A.comp (response F Q S t) + B.comp (Q t) +
        (EF.comp S - S.comp EQ + (residual A H B S).comp (Q t))) t := by
  have h := (hF.clm_comp (hasDerivAt_const t S)).sub
    ((hasDerivAt_const t S).clm_comp hQ)
  convert h using 1
  ext w
  simp [response, residual]
  abel

theorem derivative
    (A : End V) (H : End W) (B S : W →L[ℝ] V)
    (F : ℝ → End V) (Q : ℝ → End W) (t : ℝ)
    (hS : residual A H B S = 0)
    (hF : HasDerivAt F (A.comp (F t)) t)
    (hQ : HasDerivAt Q (H.comp (Q t)) t) :
    HasDerivAt (response F Q S)
      (A.comp (response F Q S t) + B.comp (Q t)) t := by
  simpa [hS] using derivative_with_defects A H B S F Q 0 0 t
    (by simpa using hF) (by simpa using hQ)

theorem defect_norm (A : End V) (H : End W) (B S : W →L[ℝ] V)
    (EF : End V) (EQ Q : End W) :
    ‖EF.comp S - S.comp EQ + (residual A H B S).comp Q‖ ≤
      ‖EF‖ * ‖S‖ + ‖S‖ * ‖EQ‖ + ‖residual A H B S‖ * ‖Q‖ := by
  calc
    _ ≤ ‖EF.comp S - S.comp EQ‖ + ‖(residual A H B S).comp Q‖ := norm_add_le _ _
    _ ≤ (‖EF.comp S‖ + ‖S.comp EQ‖) + ‖(residual A H B S).comp Q‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ _ := by
      gcongr <;> apply ContinuousLinearMap.opNorm_comp_le

/-- With an exact norm-preserving input flow, the Sylvester defect is not
multiplied by the input frequency or an exponential frequency gain. -/
theorem residual_apply_bound (A : End V) (H : End W) (B S : W →L[ℝ] V)
    (Q : End W) (w : W) (hQ : ‖Q w‖ = ‖w‖) :
    ‖residual A H B S (Q w)‖ ≤ ‖residual A H B S‖ * ‖w‖ := by
  simpa [hQ] using (residual A H B S).le_opNorm (Q w)

/-- A time-varying change of variables preserves the nonlinear remainder.
At each time the caller may use time-varying `A`, `B`, and `H`; the derivative
of the chosen Sylvester map must be charged. -/
theorem transformed_derivative (A : End V) (H : End W) (B : W →L[ℝ] V)
    (S : ℝ → (W →L[ℝ] V)) (SD : W →L[ℝ] V) (x : ℝ → V) (u : ℝ → W)
    (r : V) (t : ℝ)
    (hS : HasDerivAt S SD t)
    (hx : HasDerivAt x (A (x t)+B (u t)+r) t)
    (hu : HasDerivAt u (H (u t)) t) :
    HasDerivAt (fun s => x s+S s (u s))
      (A (x t+S t (u t))+r-(residual A H B (S t)-SD) (u t)) t := by
  convert hx.add (hS.clm_apply hu) using 1
  simp [residual]
  abel

/-- One classical inverse-frequency correction. It is included as a
frequency-aware comparator, not claimed as a new geometric construction. -/
def frequencyStep (A : End V) (J : End W) (B S : W →L[ℝ] V) : W →L[ℝ] V :=
  (A.comp S - B).comp J

theorem frequencyStep_residual (A : End V) (H J : End W) (B S : W →L[ℝ] V)
    (hJH : J.comp H = 1) (hHJ : H.comp J = 1) :
    residual A H B (frequencyStep A J B S) = A.comp ((residual A H B S).comp J) := by
  ext w
  have hjh : J (H w) = w := by simpa using congrArg (fun L : End W => L w) hJH
  have hhj : H (J w) = w := by simpa using congrArg (fun L : End W => L w) hHJ
  simp [residual, frequencyStep, hjh, hhj]
  abel

theorem frequencyStep_bound (A : End V) (H J : End W) (B S : W →L[ℝ] V)
    (hJH : J.comp H = 1) (hHJ : H.comp J = 1) :
    ‖residual A H B (frequencyStep A J B S)‖ ≤
      ‖A‖ * ‖residual A H B S‖ * ‖J‖ := by
  rw [frequencyStep_residual A H J B S hJH hHJ, mul_assoc]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg A))

/-- A real harmonic generator reduces the Sylvester solve to a solve with
`A² + frequency² I`. Both identities involving `R` are certificate premises,
so near resonance is not silently treated as invertible. -/
theorem harmonic_solver
    (A R : End V) (H : End W) (B : W →L[ℝ] V) (frequency : ℝ)
    (hH : H.comp H = -(frequency ^ 2) • (1 : End W))
    (hcommute : A.comp R = R.comp A)
    (hinverse : R.comp (A.comp A + frequency ^ 2 • (1 : End V)) = 1) :
    residual A H B (R.comp (A.comp B + B.comp H)) = 0 := by
  ext w
  have hc (v : V) : A (R v) = R (A v) := congrArg (fun L : End V => L v) hcommute
  have hi (v : V) : R (A (A v) + frequency ^ 2 • v) = v := by
    simpa using congrArg (fun L : End V => L v) hinverse
  have hh : H (H w) = -(frequency ^ 2) • w := by
    simpa using congrArg (fun L : End W => L w) hH
  simp only [residual, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply]
  rw [hc, map_add, map_add, hh]
  have hv := hi (B w)
  simp only [map_add, map_smul, neg_smul, map_neg] at hv ⊢
  calc
    _ = (R (A (A (B w))) + frequency ^ 2 • R (B w)) - B w := by abel
    _ = 0 := sub_eq_zero.mpr hv

end GNC.SylvesterResponse
