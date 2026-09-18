import GNC.Applications.OrbitalComparison.CenteredResponseData.Transfer
import GNC.Applications.OrbitalComparison.JointErrorReference
import GNC.Dynamics.GravityUnitReferenceApproximation

/-! Transfer the checked Cartesian coefficient operators to the exact
physical nominal. The oscillator residual supplies the reference error;
the polynomial reference is never treated as exactly unit length. -/
noncomputable section
namespace GNC.OrbitalComparison.CenteredResponseData
open CartesianResponsePolynomial Matrix Set
open scoped RealInnerProductSpace

abbrev E3 := SpatialBurn.E3
def nominal (t : ℝ) : E3 := WithLp.toLp 2 (JointErrorData.exactReference t)
def polynomialNominal (t : ℝ) : E3 := WithLp.toLp 2 (value reference t)

theorem phase_error {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖PolynomialPhaseCertificate.candidate phaseData t-
      RotationPhaseCertificate.phase (JointErrorData.phase t)‖≤(phaseError:ℝ)*t := by
  apply PolynomialPhaseCertificate.certifies phaseData phase_checked
    JointErrorData.phase (by simp [JointErrorData.phase]) _ ht
  intro s _
  exact JointErrorData.phase_derivative s

theorem reference_components (t : ℝ) : value reference t=
    ![PolynomialOrder.value phaseData.cosine t,PolynomialOrder.value phaseData.sine t,0] := by
  ext i
  fin_cases i <;> rfl

theorem nominal_norm (t : ℝ) : ‖nominal t‖=1 := JointErrorData.exactReference_norm t

/-- This is a spatial norm bound, with no componentwise square-root loss. -/
theorem reference_error_time {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖nominal t-polynomialNominal t‖≤(phaseError:ℝ)*t := by
  have he : ‖nominal t-polynomialNominal t‖=
      ‖PolynomialPhaseCertificate.candidate phaseData t-
        RotationPhaseCertificate.phase (JointErrorData.phase t)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change enorm (JointErrorData.exactReference t-value reference t)^2=_
    rw [enorm_sq,Complex.sq_norm,reference_components]
    simp [JointErrorData.exactReference,lengthSq,PolynomialPhaseCertificate.candidate,
      PolynomialPhaseCertificate.pair,RotationPhaseCertificate.phase,Complex.normSq_apply]
    ring
  rw [he]
  exact phase_error ht

theorem reference_error {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖nominal t-polynomialNominal t‖≤(phaseError:ℝ) := by
  have hn : (0:ℝ)≤phaseError := by exact_mod_cast phase_nonnegative
  exact (reference_error_time ht).trans (mul_le_of_le_one_right hn ht.2)

theorem gradient_transfer (y : E3) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖Gravity.gradient (K:ℝ) (nominal t) y-
      Gravity.unitGradient (K:ℝ) (polynomialNominal t) y‖≤(gradientError:ℝ)*‖y‖ := by
  have hk : (0:ℝ)≤K := by exact_mod_cast K_nonnegative
  have he : 3*(K:ℝ)*(phaseError:ℝ)*(2+(phaseError:ℝ))=(gradientError:ℝ) := by
    exact_mod_cast gradient_budget_checked
  simpa only [he] using Gravity.gradient_unit_approximation (K:ℝ) hk
    (nominal t) (polynomialNominal t) y (nominal_norm t) (reference_error ht)

theorem half_hessian_transfer (u v : E3) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(1/2:ℝ) • (Gravity.hessian (K:ℝ) (nominal t) u v-
      Gravity.unitHessian (K:ℝ) (polynomialNominal t) u v)‖≤
      (halfHessianError:ℝ)*‖u‖*‖v‖ := by
  have hk : (0:ℝ)≤K := by exact_mod_cast K_nonnegative
  have he : (K:ℝ)*(phaseError:ℝ)*
      (9+15*(1+(1+(phaseError:ℝ))+(1+(phaseError:ℝ))^2))/2=(halfHessianError:ℝ) := by
    exact_mod_cast hessian_budget_checked
  simpa only [he] using Gravity.half_hessian_unit_approximation (K:ℝ) hk
    (nominal t) (polynomialNominal t) u v (nominal_norm t) (reference_error ht)

private theorem polynomial_zero (p : List ℚ) (hp : BernsteinPolynomial.zero p) (t : ℝ) :
    PolynomialOrder.value p t=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha := hp a (by simp)
    have ht := ih (fun b hb => hp b (by simp [hb]))
    change (a:ℝ)+t*PolynomialOrder.value p t=0
    simp [ha,ht]

theorem radial_value (t : ℝ) :
    PolynomialOrder.value radialPolynomial t=JointErrorData.radialForce t := by
  have h := polynomial_zero _ radial_formula_checked t
  rw [PolynomialOrder.value_subtract,PolynomialOrder.value_subtract,scalar_multiply] at h
  have hr : phaseData.rate=JointErrorData.referenceRate := rfl
  have hk : K=JointErrorData.modelInput.K := rfl
  have hv : PolynomialOrder.value [K] t=(K:ℝ) := by
    simp [PolynomialOrder.value,Planning.PolynomialKernel.evaluate]
  rw [hv,hr] at h
  simpa only [JointErrorData.radialForce,pow_two,←hk] using sub_eq_zero.mp h

theorem radial_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    |JointErrorData.radialForce t|+(slope:ℝ)≤(forceFactor:ℝ) := by
  have h := PolynomialBounds.bound_sound radialPolynomial
    (show |t|≤(1:ℚ) from by simpa [abs_of_nonneg ht.1] using ht.2)
  change |PolynomialOrder.value radialPolynomial t|≤_ at h
  rw [radial_value] at h
  have he : (PolynomialBounds.bound radialPolynomial 1:ℝ)+(slope:ℝ)=(forceFactor:ℝ) := by
    exact_mod_cast force_factor_checked
  rw [←he]
  exact add_le_add h le_rfl

theorem force_value (t : ℝ) : value forcePolynomial t=
    JointErrorData.radialForce t • value reference t+
      (slope:ℝ) • JointErrorData.planarSpin (value reference t) := by
  ext i
  fin_cases i
  · change PolynomialOrder.value (PolynomialBounds.subtract _ _) t=_
    rw [PolynomialOrder.value_subtract,scalar_multiply,PolynomialOrder.value_scale,radial_value]
    simp [JointErrorData.planarSpin,value,PolynomialAffine.value,PolynomialOrder.value]
    ring
  · change PolynomialOrder.value (PolynomialBounds.add _ _) t=_
    rw [PolynomialOrder.value_add,scalar_multiply,PolynomialOrder.value_scale,radial_value]
    rfl
  · change (0:ℝ)=JointErrorData.radialForce t*0+(slope:ℝ)*0
    ring

theorem source_value (j : Fin 8) (t : ℝ) (i : Fin 3) :
    value (sources j) t i=
      if i=featureRow j then value forcePolynomial t (featureColumn j) else 0 := by
  have h := polynomial_zero _ (source_coefficients_checked j i) t
  rw [PolynomialOrder.value_subtract] at h
  split_ifs with hi
  · simpa only [hi,ite_true] using sub_eq_zero.mp h
  · simpa only [hi,ite_false] using sub_eq_zero.mp h

/-- Includes both radial balance and the varying-rate tangential force. -/
theorem force_transfer {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (JointErrorData.exactForce t-value forcePolynomial t)≤
      (forceFactor:ℝ)*(phaseError:ℝ) := by
  rw [force_value]
  let e := JointErrorData.exactReference t-value reference t
  have he : JointErrorData.exactForce t-
      (JointErrorData.radialForce t • value reference t+
        (slope:ℝ) • JointErrorData.planarSpin (value reference t))=
      JointErrorData.radialForce t • e+(slope:ℝ) • JointErrorData.planarSpin e := by
    ext i
    fin_cases i <;> simp [JointErrorData.exactForce,e,JointErrorData.planarSpin,
      slope,vecHead,vecTail,Pi.smul_apply,smul_eq_mul] <;> ring
  rw [he]
  have hs : (0:ℝ)≤slope := by exact_mod_cast slope_nonnegative
  have hb : enorm e≤(phaseError:ℝ) := reference_error ht
  calc
    _≤enorm (JointErrorData.radialForce t • e)+enorm ((slope:ℝ) • JointErrorData.planarSpin e) :=
      enorm_add_le _ _
    _=|JointErrorData.radialForce t| * enorm e+(slope:ℝ)*enorm (JointErrorData.planarSpin e) := by
      rw [enorm_smul,enorm_smul,abs_of_nonneg hs]
    _≤(|JointErrorData.radialForce t|+(slope:ℝ))*enorm e := by
      have h := mul_le_mul_of_nonneg_left (JointErrorData.planarSpin_bound e) hs
      nlinarith
    _≤(forceFactor:ℝ)*(phaseError:ℝ) :=
      mul_le_mul (radial_bound ht) hb (enorm_nonneg e)
        ((add_nonneg (abs_nonneg _) hs).trans (radial_bound ht))

theorem exact_force_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (JointErrorData.exactForce t)≤(forceFactor:ℝ) := by
  have hs : (0:ℝ)≤slope := by exact_mod_cast slope_nonnegative
  have h := enorm_add_le
    (JointErrorData.radialForce t • JointErrorData.exactReference t)
    ((slope:ℝ) • JointErrorData.planarSpin (JointErrorData.exactReference t))
  rw [enorm_smul,enorm_smul,abs_of_nonneg hs,JointErrorData.exactReference_norm,mul_one] at h
  have hp := JointErrorData.planarSpin_bound (JointErrorData.exactReference t)
  rw [JointErrorData.exactReference_norm] at hp
  simpa only [JointErrorData.exactForce,slope,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
    (h.trans (add_le_add le_rfl (mul_le_of_le_one_right hs hp))).trans (radial_bound ht)

end GNC.OrbitalComparison.CenteredResponseData
