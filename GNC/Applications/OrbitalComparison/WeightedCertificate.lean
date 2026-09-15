import GNC.Applications.OrbitalComparison.UniformRepresentations
import GNC.Applications.OrbitalComparison.WeightedPrediction
import GNC.Analysis.TimePolynomial

/-! A common exact-rational checker retaining the time profile of the
stored-coefficient defect and cubic gravity remainder. Both representations
use the same physical error theorem and polynomial supersolution check.
-/
namespace GNC.OrbitalComparison.WeightedCertificate
open UniformCertificate PoweredCircle Set Planning.PolynomialKernel

structure TimeRepresentation {C : Type} (A : Representation C) where
  envelope : C → List ℚ
  nonnegative : ∀ p, PolynomialOrder.nonnegative (envelope p)
  sound : ∀ p {t θ : ℝ}, 0 ≤ t → |θ| ≤ (angle:ℝ) →
    |A.value p t θ| ≤ PolynomialOrder.value (envelope p) t

noncomputable def circleTime : TimeRepresentation circleRepresentation where
  envelope := fun p => TimePolynomial.circle p angle
  nonnegative := fun p => TimePolynomial.circle_nonnegative p (by norm_num [angle])
  sound := fun p {_ _} ht hθ => TimePolynomial.circle_sound p ht hθ

noncomputable def polynomialTime : TimeRepresentation polynomialRepresentation where
  envelope := fun p => TimePolynomial.bivariate p angle
  nonnegative := fun p => TimePolynomial.bivariate_nonnegative p (by norm_num [angle])
  sound := fun p {_ _} ht hθ => TimePolynomial.bivariate_sound p ht hθ

variable {C : Type} {A : Representation C} (S : TimeRepresentation A)

theorem residualX_bound (x y : C) {t θ : ℝ} (ht : 0 ≤ t) (hθ : |θ| ≤ (angle:ℝ)) :
    |(curve A x y θ).residualX θ t| ≤ PolynomialOrder.value (S.envelope (residualX A x y)) t+
      (force:ℝ)*(A.sourceError:ℝ) := by
  rw [residualX_value]
  have hf : (0:ℝ) ≤ force := by exact_mod_cast constants.2.2.2
  have hb := mul_le_mul_of_nonneg_left (A.cosine_error t θ hθ) hf
  have he : |(force:ℝ)*(1-Real.cos θ-A.value A.cosineDifference t θ)| ≤
      (force:ℝ)*(A.sourceError:ℝ) := by simpa only [abs_mul,abs_of_nonneg hf] using hb
  exact (abs_add_le _ _).trans (add_le_add (S.sound _ ht hθ) he)

theorem residualY_bound (x y : C) {t θ : ℝ} (ht : 0 ≤ t) (hθ : |θ| ≤ (angle:ℝ)) :
    |(curve A x y θ).residualY θ t| ≤ PolynomialOrder.value (S.envelope (residualY A x y)) t+
      (force:ℝ)*(A.sourceError:ℝ) := by
  rw [residualY_value]
  have hf : (0:ℝ) ≤ force := by exact_mod_cast constants.2.2.2
  have hb := mul_le_mul_of_nonneg_left (A.sine_error t θ hθ) hf
  have he : |-((force:ℝ)*(Real.sin θ-A.value A.sine t θ))| ≤
      (force:ℝ)*(A.sourceError:ℝ) := by simpa only [abs_neg,abs_mul,abs_of_nonneg hf] using hb
  simpa only [sub_eq_add_neg] using (abs_add_le _ _).trans (add_le_add (S.sound _ ht hθ) he)

def cubicCoefficient (M : ℚ) : ℚ := 360000*(4*Direct.gravityParameter/(7000000-M)^5)*M^3

def neededForcing (x y : C) (M : ℚ) : List ℚ :=
  PolynomialBounds.add
    (PolynomialBounds.scale 7000000
      (PolynomialBounds.add (PolynomialBounds.add (S.envelope (residualX A x y))
        (S.envelope (residualY A x y))) [2*force*A.sourceError]))
    [0,0,0,0,0,0,cubicCoefficient M]

theorem neededForcing_value (x y : C) (M : ℚ) (t : ℝ) :
    PolynomialOrder.value (neededForcing S x y M) t =
      7000000*(PolynomialOrder.value (S.envelope (residualX A x y)) t+
        PolynomialOrder.value (S.envelope (residualY A x y)) t+2*(force:ℝ)*(A.sourceError:ℝ))+
      360000*(4*mu/(7000000-(M:ℝ))^5)*(M:ℝ)^3*t^6 := by
  have hs (a : ℚ) : PolynomialOrder.value [a] t = (a:ℝ) := by
    simp [PolynomialOrder.value,evaluate]
  have hm : PolynomialOrder.value [0,0,0,0,0,0,cubicCoefficient M] t =
      (cubicCoefficient M:ℝ)*t^6 := by
    norm_num [PolynomialOrder.value,evaluate]
    ring
  simp only [neededForcing,PolynomialOrder.value_add,PolynomialOrder.value_scale,hs,hm]
  norm_num [cubicCoefficient,mu,Direct.gravityParameter]

structure Data where
  x : C
  y : C
  radius : ℚ
  forcing : List ℚ
  envelope : List ℚ
  positionLimit : ℚ
  velocityLimit : ℚ

def Data.Valid (D : Data (C := C)) : Prop :=
  0 ≤ D.radius ∧ D.radius < 7000000 ∧ Direct.tubeRadius ≤ D.radius ∧
  360000*(2*Direct.gravityParameter/(7000000-D.radius)^3) ≤ 17/20 ∧
  A.bound D.x 0 = 0 ∧ A.bound D.y 0 = 0 ∧
  A.bound (A.derivative D.x) 0 = 0 ∧ A.bound (A.derivative D.y) 0 = 0 ∧
  S.envelope D.x = 0::0::(S.envelope D.x).drop 2 ∧
  S.envelope D.y = 0::0::(S.envelope D.y).drop 2 ∧
  7000000^2*((evaluate (S.envelope D.x) 1)^2+(evaluate (S.envelope D.y) 1)^2) ≤ D.radius^2 ∧
  PolynomialOrder.prefixes 0 (PolynomialBounds.subtract D.forcing (neededForcing S D.x D.y D.radius)) ∧
  PolynomialEnvelope.Valid D.forcing D.envelope ∧
  evaluate D.envelope 1 ≤ D.positionLimit ∧
  evaluate (differentiate D.envelope) 1/600 ≤ D.velocityLimit

instance (D : Data (C := C)) : Decidable (D.Valid S) := by
  unfold Data.Valid
  infer_instance

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem candidate_profile (x y : C) (M : ℚ) (hM : 0 ≤ M) (B : Plane E) {θ t : ℝ}
    (hx : S.envelope x = 0::0::(S.envelope x).drop 2)
    (hy : S.envelope y = 0::0::(S.envelope y).drop 2)
    (hr : 7000000^2*((evaluate (S.envelope x) 1)^2+(evaluate (S.envelope y) 1)^2) ≤ M^2)
    (hθ : |θ| ≤ (angle:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(curve A x y θ).position B t‖ ≤ (M:ℝ)*t^2 := by
  have hxb := (S.sound x ht.1 hθ).trans (PolynomialOrder.quadratic_time_bound _ (S.nonnegative x) hx ht)
  have hyb := (S.sound y ht.1 hθ).trans (PolynomialOrder.quadratic_time_bound _ (S.nonnegative y) hy ht)
  have hh := square_sum_bound hxb hyb
  have hr' : (7000000:ℝ)^2*(PolynomialOrder.value (S.envelope x) 1^2+
      PolynomialOrder.value (S.envelope y) 1^2) ≤ (M:ℝ)^2 := by
    have he := PolynomialOrder.value_at_rational (S.envelope x) 1
    have hf := PolynomialOrder.value_at_rational (S.envelope y) 1
    norm_num only [Rat.cast_one] at he hf
    rw [he,hf]
    exact_mod_cast hr
  apply B.scaled_mix_bound _ _ _ (mul_nonneg (by exact_mod_cast hM) (sq_nonneg t))
  calc
    _ ≤ 7000000^2*((t^2*PolynomialOrder.value (S.envelope x) 1)^2+
        (t^2*PolynomialOrder.value (S.envelope y) 1)^2) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = t^4*(7000000^2*(PolynomialOrder.value (S.envelope x) 1^2+
        PolynomialOrder.value (S.envelope y) 1^2)) := by ring
    _ ≤ t^4*(M:ℝ)^2 := mul_le_mul_of_nonneg_left hr' (by positivity)
    _ = ((M:ℝ)*t^2)^2 := by ring

theorem physical_defect (x y : C) (M : ℚ) (B : Plane E) {θ t : ℝ}
    (hM : M < 7000000) (hr : ‖(curve A x y θ).position B t‖ ≤ (M:ℝ))
    (hp : ‖(curve A x y θ).position B t‖ ≤ (M:ℝ)*t^2)
    (hθ : |θ| ≤ (angle:ℝ)) (ht : 0 ≤ t) :
    ‖(curve A x y θ).acceleration B t-
      nonlinearAcceleration (B.reference t) ((curve A x y θ).position B t) (B.force θ t)‖ ≤
      PolynomialOrder.value (neededForcing S x y M) t := by
  have hx := residualX_bound S x y ht hθ
  have hy := residualY_bound S x y ht hθ
  have hxn := (abs_nonneg _).trans hx
  have hyn := (abs_nonneg _).trans hy
  let bx := PolynomialOrder.value (S.envelope (residualX A x y)) t+(force:ℝ)*(A.sourceError:ℝ)
  let by' := PolynomialOrder.value (S.envelope (residualY A x y)) t+(force:ℝ)*(A.sourceError:ℝ)
  have hd : ‖(curve A x y θ).acceleration B t-
      quadraticAcceleration (B.reference t) ((curve A x y θ).position B t) (B.force θ t)‖ ≤
      7000000*(bx+by') := by
    rw [PositionCurve.physical_residual]
    apply B.scaled_mix_bound _ _ _ (mul_nonneg (by norm_num) (add_nonneg hxn hyn))
    have hs := square_sum_bound hx hy
    have hh : 0 ≤ bx*by' := mul_nonneg hxn hyn
    dsimp only [bx,by'] at *
    nlinarith
  have h := numerical_gravity_profile (B.reference t) ((curve A x y θ).position B t)
    (B.force θ t) ((curve A x y θ).acceleration B t) (by exact_mod_cast hM)
    (B.reference_norm t).ge hr hp hd
  rw [neededForcing_value]
  convert h using 1 <;> dsimp [bx,by'] <;> ring

/-- A concrete polynomial certificate bounds every physical trajectory with
the defining ODE and initial data, uniformly over time and pointing angle. -/
theorem Data.certifies (D : Data (C := C)) (hD : D.Valid S) (B : Plane E) {θ : ℝ}
    (X : PhysicalDeviation B.reference (B.force θ)) (hθ : |θ| ≤ 7/20) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-(curve A D.x D.y θ).position B t‖ ≤ (D.positionLimit:ℝ) ∧
      ‖X.v t-(curve A D.x D.y θ).velocity B t‖/600 ≤ (D.velocityLimit:ℝ) := by
  rcases hD with ⟨hMn,hM,hactual,hlip,hx,hy,hdx,hdy,hpx,hpy,hr,hforcing,henv,hpos,hvel⟩
  have hθ' : |θ| ≤ (angle:ℝ) := by simpa [angle] using hθ
  have hprofile := fun t ht => candidate_profile S D.x D.y D.radius hMn B hpx hpy hr hθ' (t := t) ht
  have hradius (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖(curve A D.x D.y θ).position B t‖ ≤ (D.radius:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 ht.2 (n := 2))
      (show (0:ℝ) ≤ D.radius by exact_mod_cast hMn)
    exact (hprofile t ht).trans (by simpa only [mul_one] using hh)
  have hi : (curve A D.x D.y θ).x 0 = 0 ∧ (curve A D.x D.y θ).y 0 = 0 ∧
      (curve A D.x D.y θ).dx 0 = 0 ∧ (curve A D.x D.y θ).dy 0 = 0 :=
    ⟨zero_of_bound A _ hx hθ',zero_of_bound A _ hy hθ',
      zero_of_bound A _ hdx hθ',zero_of_bound A _ hdy hθ'⟩
  have h := X.weighted_prediction ((curve A D.x D.y θ).position B)
    ((curve A D.x D.y θ).velocity B) ((curve A D.x D.y θ).acceleration B)
    D.forcing D.envelope henv (M := (D.radius:ℝ)) (by exact_mod_cast hM)
    (by exact_mod_cast hactual) (by
      have hc : ((360000*(2*Direct.gravityParameter/(7000000-D.radius)^3):ℚ):ℝ) ≤
          ((17/20:ℚ):ℝ) := by exact_mod_cast hlip
      simpa [mu,Direct.gravityParameter] using hc)
    (fun t _ => (B.reference_norm t).ge) (by
      intro t _
      have hb := (B.force_norm θ t).trans
        (mul_le_mul_of_nonneg_left hθ (le_of_lt (lt_trans (by norm_num) thrust_bounds.1)))
      simpa only [thrust_bounds.2.1] using hb)
    (continuous_iff_continuousAt.mpr fun t => ((curve A D.x D.y θ).position_derivative B t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => ((curve A D.x D.y θ).velocity_derivative B t).continuousAt)
    (fun t _ => (curve A D.x D.y θ).position_derivative B t)
    (fun t _ => (curve A D.x D.y θ).velocity_derivative B t)
    (by simp [PositionCurve.position,Plane.mix,hi.1,hi.2.1])
    (by simp [PositionCurve.velocity,Plane.mix,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2])
    hradius (by
      intro t ht
      have hb := physical_defect S D.x D.y D.radius B hM (hradius t ht) (hprofile t ht) hθ' ht.1
      have he := PolynomialOrder.prefixes_sound _ hforcing ht
      rw [PolynomialOrder.value_subtract] at he
      exact hb.trans (sub_nonneg.mp he))
  intro t ht
  have hb := h t ht
  exact ⟨hb.1.trans (by exact_mod_cast hpos),hb.2.trans (by exact_mod_cast hvel)⟩

end
end GNC.OrbitalComparison.WeightedCertificate
