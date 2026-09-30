import GNC.Preintegration.PhysicalDefect

/-! Exact time moments for the polynomial-defect physical certificate.
All constants come from polynomial primitives, retaining the position time
weight and the affine accelerometer norm envelope. -/
noncomputable section
open Set
namespace GNC.Preintegration.CenteredFoh.Defect

def primitive (k : ℕ) (t : ℝ) : ℝ := t^(k+1)/(k+1:ℕ)
def doublePrimitive (k : ℕ) (t : ℝ) : ℝ := t^(k+2)/((k+1:ℕ)*(k+2:ℕ))
def moment (k : ℕ) (u₀ u₁ t : ℝ) : ℝ :=
  u₀*primitive k t+(u₁-u₀)*primitive (k+1) t
def doubleMoment (k : ℕ) (u₀ u₁ t : ℝ) : ℝ :=
  u₀*doublePrimitive k t+(u₁-u₀)*doublePrimitive (k+1) t

theorem primitive_derivative (k : ℕ) (t : ℝ) : HasDerivAt (primitive k) (t^k) t := by
  convert (hasDerivAt_pow (k+1) t).div_const (k+1:ℕ) using 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hn : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem doublePrimitive_derivative (k : ℕ) (t : ℝ) :
    HasDerivAt (doublePrimitive k) (primitive k t) t := by
  convert (hasDerivAt_pow (k+2) t).div_const ((k+1:ℕ)*(k+2:ℕ)) using 1
  dsimp [primitive]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have h1 : (k:ℝ)+1 ≠ 0 := by positivity
  have h2 : (k:ℝ)+2 ≠ 0 := by positivity
  field_simp

theorem moment_derivative (k : ℕ) (u₀ u₁ t : ℝ) :
    HasDerivAt (moment k u₀ u₁) (t^k*((1-t)*u₀+t*u₁)) t := by
  convert ((primitive_derivative k t).const_mul u₀).add
    ((primitive_derivative (k+1) t).const_mul (u₁-u₀)) using 1
  rw [pow_succ]
  ring

theorem doubleMoment_derivative (k : ℕ) (u₀ u₁ t : ℝ) :
    HasDerivAt (doubleMoment k u₀ u₁) (moment k u₀ u₁ t) t :=
  ((doublePrimitive_derivative k t).const_mul u₀).add
    ((doublePrimitive_derivative (k+1) t).const_mul (u₁-u₀))

theorem moment_endpoint (k : ℕ) (u₀ u₁ : ℝ) :
    moment k u₀ u₁ 1 = u₀/((k+1:ℕ)*(k+2:ℕ))+u₁/(k+2:ℕ) := by
  simp only [moment, primitive, one_pow]
  have h1 : (k:ℝ)+1 ≠ 0 := by positivity
  have h2 : (k:ℝ)+2 ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  ring

theorem doubleMoment_endpoint (k : ℕ) (u₀ u₁ : ℝ) :
    doubleMoment k u₀ u₁ 1 =
      2*u₀/((k+1:ℕ)*(k+2:ℕ)*(k+3:ℕ))+u₁/((k+2:ℕ)*(k+3:ℕ)) := by
  simp only [doubleMoment, doublePrimitive, one_pow]
  have h1 : (k:ℝ)+1 ≠ 0 := by positivity
  have h2 : (k:ℝ)+2 ≠ 0 := by positivity
  have h3 : (k:ℝ)+3 ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  ring

def rotationBudget (n : ℕ) (cr dr t : ℝ) : ℝ :=
  cr*primitive n t+dr*primitive (n+1) t
def velocityBudget (n : ℕ) (cr dr cv dv u₀ u₁ t : ℝ) : ℝ :=
  cv*primitive n t+dv*primitive (n+1) t+
    (cr/(n+1:ℕ))*moment (n+1) u₀ u₁ t+
    (dr/(n+2:ℕ))*moment (n+2) u₀ u₁ t
def positionBudget (n : ℕ) (cr dr cv dv cp u₀ u₁ scale t : ℝ) : ℝ :=
  cp*primitive n t+scale*(cv*doublePrimitive n t+dv*doublePrimitive (n+1) t+
    (cr/(n+1:ℕ))*doubleMoment (n+1) u₀ u₁ t+
    (dr/(n+2:ℕ))*doubleMoment (n+2) u₀ u₁ t)

@[simp] theorem rotationBudget_zero (n : ℕ) (cr dr : ℝ) : rotationBudget n cr dr 0 = 0 := by
  simp [rotationBudget, primitive]
@[simp] theorem velocityBudget_zero (n : ℕ) (cr dr cv dv u₀ u₁ : ℝ) :
    velocityBudget n cr dr cv dv u₀ u₁ 0 = 0 := by
  simp [velocityBudget, moment, primitive]
@[simp] theorem positionBudget_zero (n : ℕ) (cr dr cv dv cp u₀ u₁ scale : ℝ) :
    positionBudget n cr dr cv dv cp u₀ u₁ scale 0 = 0 := by
  simp [positionBudget, doubleMoment, doublePrimitive, primitive]

theorem rotationBudget_derivative (n : ℕ) (cr dr t : ℝ) :
    HasDerivAt (rotationBudget n cr dr) (cr*t^n+dr*t^(n+1)) t :=
  ((primitive_derivative n t).const_mul cr).add
    ((primitive_derivative (n+1) t).const_mul dr)

theorem velocityBudget_derivative (n : ℕ) (cr dr cv dv u₀ u₁ t : ℝ) :
    HasDerivAt (velocityBudget n cr dr cv dv u₀ u₁)
      (rotationBudget n cr dr t*((1-t)*u₀+t*u₁)+cv*t^n+dv*t^(n+1)) t := by
  convert ((((primitive_derivative n t).const_mul cv).add
    ((primitive_derivative (n+1) t).const_mul dv)).add
      ((moment_derivative (n+1) u₀ u₁ t).const_mul (cr/(n+1:ℕ)))).add
        ((moment_derivative (n+2) u₀ u₁ t).const_mul (dr/(n+2:ℕ))) using 1
  dsimp [rotationBudget, primitive]
  ring

theorem positionBudget_derivative (n : ℕ) (cr dr cv dv cp u₀ u₁ scale t : ℝ) :
    HasDerivAt (positionBudget n cr dr cv dv cp u₀ u₁ scale)
      (scale*velocityBudget n cr dr cv dv u₀ u₁ t+cp*t^n) t := by
  have hi := ((((doublePrimitive_derivative n t).const_mul cv).add
      ((doublePrimitive_derivative (n+1) t).const_mul dv)).add
        ((doubleMoment_derivative (n+1) u₀ u₁ t).const_mul (cr/(n+1:ℕ)))).add
          ((doubleMoment_derivative (n+2) u₀ u₁ t).const_mul (dr/(n+2:ℕ)))
  convert ((primitive_derivative n t).const_mul cp).add (hi.const_mul scale) using 1
  dsimp [velocityBudget]
  ring

/-- Single-hold endpoint certificate with polynomial defect envelopes.
The scalar constants bound defects of finite, known predictors, not the
unknown state error. All three budgets follow from the physical ODEs. -/
theorem polynomial_physical_defect_bound {scale : ℝ} (hscale : 0 ≤ scale)
    (n : ℕ) (cr₀ cr₁ cv₀ cv₁ cp₀ u₀ u₁ : ℝ)
    (R : ℝ → SO3) (Qr dr : ℝ → Op)
    (v Qv p Qp u dv dp : ℝ → E3) (ω : ℝ → Vec3)
    (hR : ∀ t ∈ Icc 0 1,
      HasDerivAt (fun s => rotation (R s)) (rotation (R t)*hat (ω t)) t)
    (hQr : ∀ t ∈ Icc 0 1, HasDerivAt Qr (Qr t*hat (ω t)+dr t) t)
    (hv : ∀ t ∈ Icc 0 1, HasDerivAt v (rotation (R t) (u t)) t)
    (hQv : ∀ t ∈ Icc 0 1, HasDerivAt Qv (Qr t (u t)+dv t) t)
    (hp : ∀ t ∈ Icc 0 1, HasDerivAt p (scale • v t) t)
    (hQp : ∀ t ∈ Icc 0 1, HasDerivAt Qp (scale • Qv t+dp t) t)
    (hR0 : Qr 0 = rotation (R 0)) (hv0 : v 0 = Qv 0) (hp0 : p 0 = Qp 0)
    (hbr : ∀ t ∈ Icc 0 1,
      GNC.EuclideanOperator.frobenius (dr t) ≤ cr₀*t^n+cr₁*t^(n+1))
    (hbv : ∀ t ∈ Icc 0 1, ‖dv t‖ ≤ cv₀*t^n+cv₁*t^(n+1))
    (hbp : ∀ t ∈ Icc 0 1, ‖dp t‖ ≤ cp₀*t^n)
    (hbar : ∀ t ∈ Icc 0 1, ‖u t‖ ≤ (1-t)*u₀+t*u₁) :
    GNC.EuclideanOperator.frobenius (rotation (R 1)-Qr 1) ≤ rotationBudget n cr₀ cr₁ 1 ∧
      ‖v 1-Qv 1‖ ≤ velocityBudget n cr₀ cr₁ cv₀ cv₁ u₀ u₁ 1 ∧
      ‖p 1-Qp 1‖ ≤ positionBudget n cr₀ cr₁ cv₀ cv₁ cp₀ u₀ u₁ scale 1 := by
  have h := physical_defect_bound hscale R Qr dr v Qv p Qp u dv dp ω
    (rotationBudget n cr₀ cr₁) (velocityBudget n cr₀ cr₁ cv₀ cv₁ u₀ u₁)
    (positionBudget n cr₀ cr₁ cv₀ cv₁ cp₀ u₀ u₁ scale)
    (fun t => cr₀*t^n+cr₁*t^(n+1)) (fun t => cv₀*t^n+cv₁*t^(n+1))
    (fun t => cp₀*t^n) (fun t => (1-t)*u₀+t*u₁)
    hR hQr hv hQv hp hQp hR0 hv0 hp0
    (rotationBudget_zero _ _ _) (velocityBudget_zero _ _ _ _ _ _ _)
    (positionBudget_zero _ _ _ _ _ _ _ _ _)
    (rotationBudget_derivative _ _ _) (fun t => by
      convert velocityBudget_derivative n cr₀ cr₁ cv₀ cv₁ u₀ u₁ t using 1
      ring)
    (positionBudget_derivative _ _ _ _ _ _ _ _ _) hbr hbv hbp hbar
  exact h 1 ⟨by norm_num, le_rfl⟩

end GNC.Preintegration.CenteredFoh.Defect
