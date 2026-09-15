import GNC.Applications.OrbitalComparison.CircularResidual

/-! A common certificate format for finite-burn polynomial predictors.
The coefficient representation supplies proved arithmetic, differentiation,
range bounds, and sine/cosine verification errors. All remaining obligations
are exact rational comparisons, including the physical radius and final
position/inertial-velocity budgets. A coefficient generator is not trusted.
-/
namespace GNC.OrbitalComparison.UniformCertificate
open PoweredCircle Set

def angle : ℚ := 7/20
def omega : ℚ := 600*Direct.angularSpeed
def gravity : ℚ := 360000*Direct.gravityParameter/7000000^3
def force : ℚ := 360000*Direct.thrust/7000000

theorem constants : (omega:ℝ) = rate ∧ (gravity:ℝ) = gradientScale ∧
    (force:ℝ) = forceScale ∧ 0 ≤ force := by
  norm_num [omega,gravity,force,rate,gradientScale,forceScale,thrust,mu,
    Direct.angularSpeed,Direct.gravityParameter,Direct.thrust,Direct.referenceRadius]

/-- Exactly the interface required by the common checker. Both concrete
representations below prove these obligations from their coefficient lists. -/
structure Representation (C : Type) where
  add : C → C → C
  multiply : C → C → C
  scale : ℚ → C → C
  derivative : C → C
  bound : C → ℚ → ℚ
  value : C → ℝ → ℝ → ℝ
  sine : C
  cosineDifference : C
  sourceError : ℚ
  value_add : ∀ p q t θ, value (add p q) t θ = value p t θ+value q t θ
  value_multiply : ∀ p q t θ, value (multiply p q) t θ = value p t θ*value q t θ
  value_scale : ∀ a p t θ, value (scale a p) t θ = (a:ℝ)*value p t θ
  value_derivative : ∀ p t θ, HasDerivAt (fun s => value p s θ) (value (derivative p) t θ) t
  bound_sound : ∀ p {h : ℚ} {t θ : ℝ}, |t| ≤ (h:ℝ) → |θ| ≤ (angle:ℝ) →
    |value p t θ| ≤ (bound p h:ℝ)
  sine_error : ∀ t θ, |θ| ≤ (angle:ℝ) →
    |Real.sin θ-value sine t θ| ≤ (sourceError:ℝ)
  cosine_error : ∀ t θ, |θ| ≤ (angle:ℝ) →
    |1-Real.cos θ-value cosineDifference t θ| ≤ (sourceError:ℝ)

variable {C : Type} (A : Representation C)

def residualX (x y : C) : C :=
  A.add (A.add (A.add (A.add (A.add
    (A.derivative (A.derivative x)) (A.scale (-2*omega) (A.derivative y)))
    (A.scale (-omega^2-2*gravity) x)) (A.scale (3*gravity) (A.multiply x x)))
    (A.scale (-(3/2)*gravity) (A.multiply y y))) (A.scale force A.cosineDifference)
def residualY (x y : C) : C :=
  A.add (A.add (A.add (A.add (A.derivative (A.derivative y))
    (A.scale (2*omega) (A.derivative x))) (A.scale (gravity-omega^2) y))
    (A.scale (-3*gravity) (A.multiply x y))) (A.scale (-force) A.sine)

def curve (x y : C) (θ : ℝ) : PositionCurve where
  x := fun t => A.value x t θ
  y := fun t => A.value y t θ
  dx := fun t => A.value (A.derivative x) t θ
  dy := fun t => A.value (A.derivative y) t θ
  ddx := fun t => A.value (A.derivative (A.derivative x)) t θ
  ddy := fun t => A.value (A.derivative (A.derivative y)) t θ
  derivative_x := fun t => A.value_derivative x t θ
  derivative_y := fun t => A.value_derivative y t θ
  derivative_dx := fun t => A.value_derivative (A.derivative x) t θ
  derivative_dy := fun t => A.value_derivative (A.derivative y) t θ

theorem residualX_value (x y : C) (t θ : ℝ) :
    (curve A x y θ).residualX θ t = A.value (residualX A x y) t θ+
      (force:ℝ)*(1-Real.cos θ-A.value A.cosineDifference t θ) := by
  simp only [curve,PositionCurve.residualX,residualX,A.value_add,A.value_scale,
    A.value_multiply,Rat.cast_neg,Rat.cast_mul,Rat.cast_sub,Rat.cast_pow,
    Rat.cast_div,Rat.cast_ofNat,constants.1,constants.2.1,constants.2.2.1]
  ring
theorem residualY_value (x y : C) (t θ : ℝ) :
    (curve A x y θ).residualY θ t = A.value (residualY A x y) t θ-
      (force:ℝ)*(Real.sin θ-A.value A.sine t θ) := by
  simp only [curve,PositionCurve.residualY,residualY,A.value_add,A.value_scale,
    A.value_multiply,Rat.cast_neg,Rat.cast_mul,Rat.cast_sub,Rat.cast_pow,
    Rat.cast_div,Rat.cast_ofNat,constants.1,constants.2.1,constants.2.2.1]
  ring

def xDefect (x y : C) : ℚ := A.bound (residualX A x y) 1+force*A.sourceError
def yDefect (x y : C) : ℚ := A.bound (residualY A x y) 1+force*A.sourceError

theorem residualX_bound (x y : C) {t θ : ℝ} (ht : |t| ≤ 1) (hθ : |θ| ≤ (angle:ℝ)) :
    |(curve A x y θ).residualX θ t| ≤ (xDefect A x y:ℝ) := by
  rw [residualX_value]
  have hf : (0:ℝ) ≤ force := by exact_mod_cast constants.2.2.2
  have hb := mul_le_mul_of_nonneg_left (A.cosine_error t θ hθ) hf
  have hp := A.bound_sound (residualX A x y) (h := 1) (by simpa using ht) hθ
  have he : |(force:ℝ)*(1-Real.cos θ-A.value A.cosineDifference t θ)| ≤
      (force:ℝ)*(A.sourceError:ℝ) := by
    simpa only [abs_mul,abs_of_nonneg hf] using hb
  have h := (abs_add_le _ _).trans (add_le_add hp he)
  simpa only [xDefect,Rat.cast_add,Rat.cast_mul] using h
theorem residualY_bound (x y : C) {t θ : ℝ} (ht : |t| ≤ 1) (hθ : |θ| ≤ (angle:ℝ)) :
    |(curve A x y θ).residualY θ t| ≤ (yDefect A x y:ℝ) := by
  rw [residualY_value]
  have hf : (0:ℝ) ≤ force := by exact_mod_cast constants.2.2.2
  have hb := mul_le_mul_of_nonneg_left (A.sine_error t θ hθ) hf
  have hp := A.bound_sound (residualY A x y) (h := 1) (by simpa using ht) hθ
  have he : |-((force:ℝ)*(Real.sin θ-A.value A.sine t θ))| ≤
      (force:ℝ)*(A.sourceError:ℝ) := by
    simpa only [abs_neg,abs_mul,abs_of_nonneg hf] using hb
  have h := (abs_add_le _ _).trans (add_le_add hp he)
  simpa only [yDefect,Rat.cast_add,Rat.cast_mul,sub_eq_add_neg] using h

def accelerationBudget (M d : ℚ) : ℚ :=
  7000000*d+360000*(4*Direct.gravityParameter/(7000000-M)^5)*M^3

structure Data where
  x : C
  y : C
  radius : ℚ
  defect : ℚ
  positionLimit : ℚ
  velocityLimit : ℚ

def Data.Valid (D : Data (C := C)) : Prop :=
  D.radius < 7000000 ∧ Direct.tubeRadius ≤ D.radius ∧ 0 ≤ D.defect ∧
  360000*(2*Direct.gravityParameter/(7000000-D.radius)^3) ≤ 17/20 ∧
  A.bound D.x 0 = 0 ∧ A.bound D.y 0 = 0 ∧
  A.bound (A.derivative D.x) 0 = 0 ∧ A.bound (A.derivative D.y) 0 = 0 ∧
  7000000^2*((A.bound D.x 1)^2+(A.bound D.y 1)^2) ≤ D.radius^2 ∧
  (xDefect A D.x D.y)^2+(yDefect A D.x D.y)^2 ≤ D.defect^2 ∧
  Direct.positionGain*accelerationBudget D.radius D.defect ≤ D.positionLimit ∧
  Direct.velocityGain/600*accelerationBudget D.radius D.defect ≤ D.velocityLimit

instance (D : Data (C := C)) : Decidable (D.Valid A) := by
  unfold Data.Valid
  infer_instance

theorem square_sum_bound {x y b c : ℝ} (hx : |x| ≤ b) (hy : |y| ≤ c) :
    x^2+y^2 ≤ b^2+c^2 := by
  simpa only [sq_abs] using add_le_add
    (pow_le_pow_left₀ (abs_nonneg x) hx 2) (pow_le_pow_left₀ (abs_nonneg y) hy 2)

theorem zero_of_bound (x : C) (hx : A.bound x 0 = 0) {θ : ℝ} (hθ : |θ| ≤ (angle:ℝ)) :
    A.value x 0 θ = 0 := by
  have h := A.bound_sound x (t := 0) (by norm_num : |(0:ℝ)| ≤ ((0:ℚ):ℝ)) hθ
  rw [hx,Rat.cast_zero] at h
  exact abs_nonpos_iff.mp h

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- All certificate bounds are checked data. Only the physical trajectory,
its defining ODE/initial data, and the actual pointing angle are supplied. -/
theorem Data.certifies (D : Data (C := C)) (hD : D.Valid A) (B : Plane E) {θ : ℝ}
    (X : PhysicalDeviation B.reference (B.force θ)) (hθ : |θ| ≤ 7/20) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-(curve A D.x D.y θ).position B t‖ ≤ (D.positionLimit:ℝ) ∧
      ‖X.v t-(curve A D.x D.y θ).velocity B t‖/600 ≤ (D.velocityLimit:ℝ) := by
  rcases hD with ⟨hM,hactual,hd,hlip,hx,hy,hdx,hdy,hr,hrd,hp,hv⟩
  have hθ' : |θ| ≤ (angle:ℝ) := by simpa [angle] using hθ
  have h := (curve A D.x D.y θ).error_bound B X hθ
    (M := (D.radius:ℝ)) (d := (D.defect:ℝ)) (by exact_mod_cast hM)
    (by exact_mod_cast hactual)
    (by
      have hc : ((360000*(2*Direct.gravityParameter/(7000000-D.radius)^3):ℚ):ℝ) ≤
          ((17/20:ℚ):ℝ) := by exact_mod_cast hlip
      simpa [mu,Direct.gravityParameter] using hc)
    (by exact_mod_cast hd)
    ⟨zero_of_bound A _ hx hθ',zero_of_bound A _ hy hθ',
      zero_of_bound A _ hdx hθ',zero_of_bound A _ hdy hθ'⟩ (by
      intro t ht
      have ht' : |t| ≤ ((1:ℚ):ℝ) := by simpa only [Rat.cast_one,abs_of_nonneg ht.1] using ht.2
      have hb := square_sum_bound (A.bound_sound D.x ht' hθ') (A.bound_sound D.y ht' hθ')
      have hc : (7000000:ℝ)^2*((A.bound D.x 1:ℝ)^2+(A.bound D.y 1:ℝ)^2) ≤ (D.radius:ℝ)^2 := by
        exact_mod_cast hr
      exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans hc) (by
      intro t ht
      have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
      have hb := square_sum_bound (residualX_bound A D.x D.y ht' hθ') (residualY_bound A D.x D.y ht' hθ')
      exact hb.trans (by exact_mod_cast hrd))
  intro t ht
  have hh := h t ht
  have he : (accelerationBudget D.radius D.defect:ℝ) =
      7000000*(D.defect:ℝ)+360000*(4*mu/(7000000-(D.radius:ℝ))^5)*(D.radius:ℝ)^3 := by
    norm_num [accelerationBudget,mu,Direct.gravityParameter]
  constructor
  · rw [← he] at hh
    exact hh.1.trans (by exact_mod_cast hp)
  · rw [← he] at hh
    exact hh.2.trans (by exact_mod_cast hv)

end
end GNC.OrbitalComparison.UniformCertificate
