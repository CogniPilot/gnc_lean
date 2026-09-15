import GNC.Applications.OrbitalComparison.HarmonicDefect

/-! An exact-rational certificate record for one phase harmonic.
Its coefficient residual, initial conditions and Frobenius envelopes are
checked independently of the solver that proposed the coefficients. -/
namespace GNC.OrbitalComparison.HarmonicMode
open HarmonicPolynomial
open HarmonicFrame (positionOperator velocityOperator)

structure Mode where
  p : Poly
  s : Coeff
  positionBounds : List ℚ
  positionFast : ℚ
  velocityBounds : List ℚ
  velocityFast : ℚ
  residualBounds : List ℚ
  residualFast : ℚ

def Mode.positionBound (M : Mode) : ℚ := M.positionBounds.sum+M.positionFast
def Mode.velocityBound (M : Mode) : ℚ := M.velocityBounds.sum+M.velocityFast
def Mode.residualBound (M : Mode) : ℚ := M.residualBounds.sum+M.residualFast

def Mode.Valid (M : Mode) (ω : ℚ) (b₀ b : Coeff) : Prop :=
  (∀ i j, M.p.headD 0 i j = M.s i j) ∧
  (∀ i j, (derivative M.p).headD 0 i j = rate ω M.s i j) ∧
  Bounds M.p M.positionBounds ∧ 0 ≤ M.positionFast ∧ squared M.s ≤ M.positionFast^2 ∧
  Bounds (derivative M.p) M.velocityBounds ∧ 0 ≤ M.velocityFast ∧
    squared (rate ω M.s) ≤ M.velocityFast^2 ∧
  Bounds (residual positionOperator velocityOperator M.p b₀) M.residualBounds ∧
  0 ≤ M.residualFast ∧ squared (fastResidual positionOperator velocityOperator ω M.s b) ≤
    M.residualFast^2

instance (M : Mode) (ω : ℚ) (b₀ b : Coeff) : Decidable (M.Valid ω b₀ b) := by
  unfold Mode.Valid
  infer_instance

noncomputable section
open Set

def Mode.position (M : Mode) (ω : ℚ) (φ : ℝ) : ℝ → E3 := response M.p M.s (ω:ℝ) φ
def Mode.velocity (M : Mode) (ω : ℚ) (φ : ℝ) : ℝ → E3 :=
  response (derivative M.p) (rate ω M.s) (ω:ℝ) φ
def Mode.acceleration (M : Mode) (ω : ℚ) (φ : ℝ) : ℝ → E3 :=
  response (derivative (derivative M.p)) (rate ω (rate ω M.s)) (ω:ℝ) φ

theorem Mode.derivative_position (M : Mode) (ω : ℚ) (φ t : ℝ) :
    HasDerivAt (M.position ω φ) (M.velocity ω φ t) t := response_derivative M.p M.s ω φ t

theorem Mode.derivative_velocity (M : Mode) (ω : ℚ) (φ t : ℝ) :
    HasDerivAt (M.velocity ω φ) (M.acceleration ω φ t) t :=
  response_derivative (derivative M.p) (rate ω M.s) ω φ t

theorem Mode.continuous_position (M : Mode) (ω : ℚ) (φ : ℝ) : Continuous (M.position ω φ) :=
  response_continuous M.p M.s ω φ

theorem Mode.continuous_velocity (M : Mode) (ω : ℚ) (φ : ℝ) : Continuous (M.velocity ω φ) :=
  response_continuous (derivative M.p) (rate ω M.s) ω φ

theorem Mode.initial (M : Mode) (ω : ℚ) (b₀ b : Coeff) (h : M.Valid ω b₀ b) (φ : ℝ) :
    M.position ω φ 0 = 0 ∧ M.velocity ω φ 0 = 0 :=
  response_initial M.p M.s ω φ (funext fun i => funext (h.1 i))
    (funext fun i => funext (h.2.1 i))

theorem Mode.position_bound (M : Mode) (ω : ℚ) (b₀ b : Coeff) (h : M.Valid ω b₀ b)
    (φ : ℝ) {t : ℝ} (ht : |t| ≤ 1) : ‖M.position ω φ t‖ ≤ (M.positionBound:ℝ) := by
  rcases h with ⟨_,_,hp,hf,hs,_⟩
  exact response_bound M.p M.s (ω:ℝ) φ M.positionBounds hp hf hs ht

theorem Mode.velocity_bound (M : Mode) (ω : ℚ) (b₀ b : Coeff) (h : M.Valid ω b₀ b)
    (φ : ℝ) {t : ℝ} (ht : |t| ≤ 1) : ‖M.velocity ω φ t‖ ≤ (M.velocityBound:ℝ) := by
  rcases h with ⟨_,_,_,_,_,hv,hf,hs,_⟩
  exact response_bound (derivative M.p) (rate ω M.s) (ω:ℝ) φ M.velocityBounds hv hf hs ht

theorem Mode.residual_bound (M : Mode) (ω : ℚ) (b₀ b : Coeff) (h : M.Valid ω b₀ b)
    (φ : ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    ‖M.acceleration ω φ t-linear positionOperator (M.position ω φ t)-
      linear velocityOperator (M.velocity ω φ t)-harmonic b₀ φ-harmonic b ((ω:ℝ)*t+φ)‖ ≤
      (M.residualBound:ℝ) := by
  rcases h with ⟨_,_,_,_,_,_,_,_,hr,hf,hs⟩
  exact response_residual_bound positionOperator velocityOperator M.p M.s b₀ b ω
    M.residualBounds hr hf hs ht φ

end
end GNC.OrbitalComparison.HarmonicMode
