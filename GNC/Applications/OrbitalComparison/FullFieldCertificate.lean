import GNC.Applications.OrbitalComparison.InverseRadiusResidual

/-! Common full-field certificates for stored finite-burn candidates.
The extra polynomial is an approximate inverse-radius offset. Its algebraic
constraint residual is certified; no auxiliary ODE or Taylor gravity tail is
assumed. All final comparisons are exact rational computations.
-/
namespace GNC.OrbitalComparison.FullFieldCertificate
open UniformCertificate WeightedCertificate PoweredCircle Set Planning.PolynomialKernel
variable {C : Type} (A : Representation C)

def cubic (e : C) : C := A.add (A.add (A.scale 3 e) (A.scale 3 (A.multiply e e)))
  (A.multiply (A.multiply e e) e)

def constraint (x y e : C) : C :=
  let h := A.add (A.add (A.scale 2 x) (A.multiply x x)) (A.multiply y y)
  let z := A.add (A.scale 2 e) (A.multiply e e)
  A.add (A.add h z) (A.multiply h z)

def residualX (x y e : C) : C :=
  A.add (A.add (A.add (A.add (A.derivative (A.derivative x))
    (A.scale (-2*omega) (A.derivative y))) (A.scale (-omega^2) x))
    (A.scale gravity (A.add (A.add x (cubic A e)) (A.multiply x (cubic A e)))))
    (A.scale force A.cosineDifference)
def residualY (x y e : C) : C :=
  A.add (A.add (A.add (A.add (A.derivative (A.derivative y))
    (A.scale (2*omega) (A.derivative x))) (A.scale (-omega^2) y))
    (A.scale gravity (A.add y (A.multiply y (cubic A e))))) (A.scale (-force) A.sine)

theorem cubic_value (e : C) (t θ : ℝ) :
    A.value (cubic A e) t θ = inverseCubic (A.value e t θ) := by
  simp only [cubic,A.value_add,A.value_scale,A.value_multiply,Rat.cast_ofNat,inverseCubic]
  ring

theorem constraint_value (x y e : C) (t θ : ℝ) :
    A.value (constraint A x y e) t θ = inverseConstraint (A.value x t θ) (A.value y t θ) (A.value e t θ) := by
  simp only [constraint,A.value_add,A.value_scale,A.value_multiply,Rat.cast_ofNat,inverseConstraint]
  ring

theorem residualX_value (x y e : C) (t θ : ℝ) :
    (curve A x y θ).fullResidualX θ t (A.value e t θ) = A.value (residualX A x y e) t θ+
      (force:ℝ)*(1-Real.cos θ-A.value A.cosineDifference t θ) := by
  simp only [curve,PositionCurve.fullResidualX,residualX,A.value_add,A.value_scale,
    A.value_multiply,cubic_value,Rat.cast_neg,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
    constants.1,constants.2.1,constants.2.2.1]
  ring

theorem residualY_value (x y e : C) (t θ : ℝ) :
    (curve A x y θ).fullResidualY θ t (A.value e t θ) = A.value (residualY A x y e) t θ-
      (force:ℝ)*(Real.sin θ-A.value A.sine t θ) := by
  simp only [curve,PositionCurve.fullResidualY,residualY,A.value_add,A.value_scale,
    A.value_multiply,cubic_value,Rat.cast_neg,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
    constants.1,constants.2.1,constants.2.2.1]
  ring

def amplitude (M b : ℚ) : ℚ := ((7000000+M)/7000000)*(1+b)
def gain (M b : ℚ) : ℚ :=
  360000*Direct.gravityParameter*((amplitude M b)^2+amplitude M b+1)/
    (amplitude M b+1)/(7000000-M)^2

theorem gain_value (M b : ℚ) : (gain M b:ℝ) = inverseGain M b := by
  simp only [gain,inverseGain,amplitude,inverseAmplitude,Gravity.inverseRadiusFactor,
    Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_sub,Rat.cast_pow,Rat.cast_ofNat,
    Rat.cast_one,Direct.gravityParameter,mu]
  ring

theorem gain_nonnegative {M b : ℚ} (hM : 0 ≤ M) (hb : 0 ≤ b) : 0 ≤ gain M b := by
  unfold gain amplitude Direct.gravityParameter
  positivity

variable {A} (S : TimeRepresentation A)

def neededForcing (x y e : C) (M b : ℚ) : List ℚ :=
  PolynomialBounds.add
    (PolynomialBounds.scale 7000000
      (PolynomialBounds.add (PolynomialBounds.add (S.envelope (residualX A x y e))
        (S.envelope (residualY A x y e))) [2*force*A.sourceError]))
    (PolynomialBounds.scale (gain M b) (S.envelope (constraint A x y e)))

theorem neededForcing_value (x y e : C) (M b : ℚ) (t : ℝ) :
    PolynomialOrder.value (neededForcing S x y e M b) t =
      7000000*(PolynomialOrder.value (S.envelope (residualX A x y e)) t+
        PolynomialOrder.value (S.envelope (residualY A x y e)) t+2*(force:ℝ)*(A.sourceError:ℝ))+
      (gain M b:ℝ)*PolynomialOrder.value (S.envelope (constraint A x y e)) t := by
  have hs (a : ℚ) : PolynomialOrder.value [a] t = (a:ℝ) := by
    simp [PolynomialOrder.value,evaluate]
  simp only [neededForcing,PolynomialOrder.value_add,PolynomialOrder.value_scale,hs]
  push_cast
  ring

structure Data where
  x : C
  y : C
  inverseOffset : C
  radius : ℚ
  offsetBound : ℚ
  forcing : List ℚ
  envelope : List ℚ
  positionLimit : ℚ
  velocityLimit : ℚ

def Data.Valid (D : Data (C := C)) : Prop :=
  0 ≤ D.radius ∧ D.radius < 7000000 ∧ Direct.tubeRadius ≤ D.radius ∧
  360000*(2*Direct.gravityParameter/(7000000-D.radius)^3) ≤ 17/20 ∧
  0 ≤ D.offsetBound ∧ D.offsetBound < 1 ∧
  evaluate (S.envelope D.inverseOffset) 1 ≤ D.offsetBound ∧
  A.bound D.x 0 = 0 ∧ A.bound D.y 0 = 0 ∧
  A.bound (A.derivative D.x) 0 = 0 ∧ A.bound (A.derivative D.y) 0 = 0 ∧
  S.envelope D.x = 0::0::(S.envelope D.x).drop 2 ∧
  S.envelope D.y = 0::0::(S.envelope D.y).drop 2 ∧
  7000000^2*((evaluate (S.envelope D.x) 1)^2+(evaluate (S.envelope D.y) 1)^2) ≤ D.radius^2 ∧
  PolynomialOrder.prefixes 0 (PolynomialBounds.subtract D.forcing
    (neededForcing S D.x D.y D.inverseOffset D.radius D.offsetBound)) ∧
  PolynomialEnvelope.Valid D.forcing D.envelope ∧
  evaluate D.envelope 1 ≤ D.positionLimit ∧
  evaluate (differentiate D.envelope) 1/600 ≤ D.velocityLimit

instance (D : Data (C := C)) : Decidable (D.Valid S) := by
  unfold Data.Valid
  infer_instance

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physical_defect (x y e : C) (M b : ℚ) (B : Plane E) {θ t : ℝ}
    (hM : M < 7000000) (hb : b < 1) (he : |A.value e t θ| ≤ (b:ℝ))
    (hr : ‖(curve A x y θ).position B t‖ ≤ (M:ℝ))
    (hθ : |θ| ≤ (angle:ℝ)) (ht : 0 ≤ t) :
    ‖(curve A x y θ).acceleration B t-
      nonlinearAcceleration (B.reference t) ((curve A x y θ).position B t) (B.force θ t)‖ ≤
      PolynomialOrder.value (neededForcing S x y e M b) t := by
  have hf : (0:ℝ) ≤ force := by exact_mod_cast constants.2.2.2
  have hc := mul_le_mul_of_nonneg_left (A.cosine_error t θ hθ) hf
  have hs := mul_le_mul_of_nonneg_left (A.sine_error t θ hθ) hf
  have hx : |(curve A x y θ).fullResidualX θ t (A.value e t θ)| ≤
      PolynomialOrder.value (S.envelope (residualX A x y e)) t+(force:ℝ)*(A.sourceError:ℝ) := by
    rw [residualX_value]
    exact (abs_add_le _ _).trans (add_le_add (S.sound _ ht hθ)
      (by simpa only [abs_mul,abs_of_nonneg hf] using hc))
  have hy : |(curve A x y θ).fullResidualY θ t (A.value e t θ)| ≤
      PolynomialOrder.value (S.envelope (residualY A x y e)) t+(force:ℝ)*(A.sourceError:ℝ) := by
    rw [residualY_value]
    exact (abs_sub _ _).trans (add_le_add (S.sound _ ht hθ)
      (by simpa only [abs_mul,abs_of_nonneg hf] using hs))
  let bx := PolynomialOrder.value (S.envelope (residualX A x y e)) t+(force:ℝ)*(A.sourceError:ℝ)
  let by' := PolynomialOrder.value (S.envelope (residualY A x y e)) t+(force:ℝ)*(A.sourceError:ℝ)
  have hxn : 0 ≤ bx := (abs_nonneg _).trans hx
  have hyn : 0 ≤ by' := (abs_nonneg _).trans hy
  have hd : ‖(curve A x y θ).acceleration B t-
      B.liftedAcceleration θ t (A.value x t θ) (A.value y t θ) (A.value e t θ)‖ ≤ 7000000*(bx+by') := by
    have h := (curve A x y θ).full_residual B θ t (A.value e t θ)
    change (curve A x y θ).acceleration B t-
      B.liftedAcceleration θ t (A.value x t θ) (A.value y t θ) (A.value e t θ) = _ at h
    rw [h]
    apply B.scaled_mix_bound _ _ _ (by positivity)
    have hsq := square_sum_bound hx hy
    have hm := mul_nonneg hxn hyn
    change _ ≤ (7000000*(bx+by'))^2
    nlinarith
  have hg := B.lift_difference θ t (A.value x t θ) (A.value y t θ) (A.value e t θ)
    (by exact_mod_cast hM) hr (by exact_mod_cast hb) he
  rw [← gain_value,← constraint_value] at hg
  have hMn : (0:ℚ) ≤ M := by exact_mod_cast (norm_nonneg _).trans hr
  have hbn : (0:ℚ) ≤ b := by exact_mod_cast (abs_nonneg _).trans he
  have hgb := mul_le_mul_of_nonneg_left (S.sound (constraint A x y e) ht hθ)
    (show (0:ℝ) ≤ (gain M b:ℝ) by exact_mod_cast gain_nonnegative hMn hbn)
  have hh := (norm_sub_le_norm_sub_add_norm_sub _
    (B.liftedAcceleration θ t (A.value x t θ) (A.value y t θ) (A.value e t θ)) _).trans
      (add_le_add hd (hg.trans hgb))
  rw [neededForcing_value]
  convert hh using 1 <;> dsimp [bx,by'] <;> ring

/-- A full-gravity certificate bounds every physical trajectory with the
specified initial state and pointing error, uniformly over the entire burn. -/
theorem Data.certifies (D : Data (C := C)) (hD : D.Valid S) (B : Plane E) {θ : ℝ}
    (X : PhysicalDeviation B.reference (B.force θ)) (hθ : |θ| ≤ 7/20) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-(curve A D.x D.y θ).position B t‖ ≤ (D.positionLimit:ℝ) ∧
      ‖X.v t-(curve A D.x D.y θ).velocity B t‖/600 ≤ (D.velocityLimit:ℝ) := by
  rcases hD with ⟨hMn,hM,hactual,hlip,_hbn,hb,he,hx,hy,hdx,hdy,hpx,hpy,hr,hforcing,henv,hpos,hvel⟩
  have hθ' : |θ| ≤ (angle:ℝ) := by simpa [angle] using hθ
  have hprofile := fun t ht => candidate_profile S D.x D.y D.radius hMn B hpx hpy hr hθ' (t := t) ht
  have hradius (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖(curve A D.x D.y θ).position B t‖ ≤ (D.radius:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 ht.2 (n := 2))
      (show (0:ℝ) ≤ D.radius by exact_mod_cast hMn)
    exact (hprofile t ht).trans (by simpa only [mul_one] using hh)
  have hoffset (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : |A.value D.inverseOffset t θ| ≤ (D.offsetBound:ℝ) := by
    have h := (S.sound D.inverseOffset ht.1 hθ').trans
      (PolynomialOrder.value_le_endpoint _ (S.nonnegative D.inverseOffset) ht)
    have hp := PolynomialOrder.value_at_rational (S.envelope D.inverseOffset) 1
    rw [Rat.cast_one] at hp
    exact h.trans (hp.le.trans (by exact_mod_cast he))
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
      have hf := (B.force_norm θ t).trans
        (mul_le_mul_of_nonneg_left hθ (le_of_lt (lt_trans (by norm_num) thrust_bounds.1)))
      simpa only [thrust_bounds.2.1] using hf)
    (continuous_iff_continuousAt.mpr fun t => ((curve A D.x D.y θ).position_derivative B t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => ((curve A D.x D.y θ).velocity_derivative B t).continuousAt)
    (fun t _ => (curve A D.x D.y θ).position_derivative B t)
    (fun t _ => (curve A D.x D.y θ).velocity_derivative B t)
    (by simp [PositionCurve.position,Plane.mix,hi.1,hi.2.1])
    (by simp [PositionCurve.velocity,Plane.mix,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2])
    hradius (by
      intro t ht
      have hf := physical_defect S D.x D.y D.inverseOffset D.radius D.offsetBound B
        hM hb (hoffset t ht) (hradius t ht) hθ' ht.1
      have he := PolynomialOrder.prefixes_sound _ hforcing ht
      rw [PolynomialOrder.value_subtract] at he
      exact hf.trans (sub_nonneg.mp he))
  intro t ht
  have hh := h t ht
  exact ⟨hh.1.trans (by exact_mod_cast hpos),hh.2.trans (by exact_mod_cast hvel)⟩

end
end GNC.OrbitalComparison.FullFieldCertificate
