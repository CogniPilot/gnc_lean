import GNC.Applications.OrbitalComparison.PointingCapPolynomial
import GNC.Analysis.QuarticPointing
import GNC.Analysis.OcticPointing
import GNC.Analysis.CirclePolynomial

/-! A shared parameter-polynomial checker for retained pointing and an angle
Taylor jet. The domain and quotient identity are independent of the producer.
The unused second parameter is exactly zero in this fixed-axis comparison.
-/
namespace GNC.OrbitalComparison.VaryingRatePolynomial
open ParameterPolynomial PointingCapPolynomial SpatialBurn Set

inductive Kind | retained | quartic | octic deriving DecidableEq, Repr

def radius (σ : ℚ) : Fin 3 → ℚ := ![σ,0,σ^2/2]
def time (p : List ℚ) : Coefficients := [⟨0,0,0,p⟩]
def sine : Kind → Coefficients
  | .retained => u
  | .quartic => add u (scale (-1/6) (multiply u (multiply u u)))
  | .octic => [⟨1,0,0,[1]⟩,⟨3,0,0,[-1/6]⟩,⟨5,0,0,[1/120]⟩,⟨7,0,0,[-1/5040]⟩]
def cosineLoss : Kind → Coefficients
  | .retained => c
  | .quartic => subtract (scale (1/2) (multiply u u))
      (scale (1/24) (multiply (multiply u u) (multiply u u)))
  | .octic => [⟨2,0,0,[1/2]⟩,⟨4,0,0,[-1/24]⟩,⟨6,0,0,[1/720]⟩,⟨8,0,0,[-1/40320]⟩]
def constraint : Kind → Coefficients
  | .retained => add (subtract (multiply c c) (scale 2 c)) (multiply u u)
  | .quartic | .octic => []
def bounded (p : PointingCapPolynomial.Vector) (σ B : ℚ) : Prop :=
  0≤B ∧ (bound (p 0) (radius σ))^2+(bound (p 1) (radius σ))^2+
    (bound (p 2) (radius σ))^2≤B^2
instance (p : PointingCapPolynomial.Vector) (σ B : ℚ) : Decidable (bounded p σ B) := by
  unfold bounded
  infer_instance

noncomputable section
def parameter : Kind → ℝ → Fin 3 → ℝ
  | .retained, θ => ![Real.sin θ,0,1-Real.cos θ]
  | .quartic, θ | .octic, θ => ![θ,0,0]

theorem parameter_bound (kind : Kind) {σ : ℚ} {θ : ℝ} (hθ : |θ|≤(σ:ℝ)) :
    ∀ i, |parameter kind θ i|≤(radius σ i:ℝ) := by
  have hσ := (abs_nonneg θ).trans hθ
  have hc := CirclePolynomial.cosine_bound θ
  have hsq : θ^2≤(σ:ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg θ) hθ 2
  cases kind <;> intro i <;> fin_cases i <;> norm_num [parameter,radius]
  all_goals first | exact Real.abs_sin_le_abs.trans hθ | exact hθ | linarith | positivity

@[simp] theorem value_time (p : List ℚ) (x : Fin 3 → ℝ) (t : ℝ) :
    value (time p) x t=PolynomialOrder.value p t := by
  simp [time,value,termValue,monomial]

theorem value_constraint (kind : Kind) (θ t : ℝ) :
    value (constraint kind) (parameter kind θ) t=0 := by
  cases kind with
  | quartic | octic => rfl
  | retained =>
    simp only [constraint,value_add,value_subtract,
      value_multiply,value_scale,value_c,value_u,parameter]
    norm_num
    change (1-Real.cos θ)*(1-Real.cos θ)-2*(1-Real.cos θ)+Real.sin θ*Real.sin θ=0
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem sine_retained (θ t : ℝ) : value (sine .retained) (parameter .retained θ) t=Real.sin θ := by
  simp [sine,parameter]
theorem cosine_retained (θ t : ℝ) : value (cosineLoss .retained) (parameter .retained θ) t=1-Real.cos θ := by
  simp [cosineLoss,parameter]
theorem sine_quartic (θ t : ℝ) : value (sine .quartic) (parameter .quartic θ) t=QuarticPointing.sine θ := by
  simp [sine,value_add,value_scale,value_multiply,parameter,QuarticPointing.sine]
  ring
theorem cosine_quartic (θ t : ℝ) : value (cosineLoss .quartic) (parameter .quartic θ) t=QuarticPointing.cosineLoss θ := by
  simp [cosineLoss,value_subtract,value_scale,value_multiply,parameter,QuarticPointing.cosineLoss]
  ring

theorem sine_octic (θ t : ℝ) : value (sine .octic) (parameter .octic θ) t=OcticPointing.sine θ := by
  norm_num [sine,value,termValue,monomial,PolynomialOrder.value,
    Planning.PolynomialKernel.evaluate,parameter,OcticPointing.sine]
  ring
theorem cosine_octic (θ t : ℝ) : value (cosineLoss .octic) (parameter .octic θ) t=OcticPointing.cosineLoss θ := by
  norm_num [cosineLoss,value,termValue,monomial,PolynomialOrder.value,
    Planning.PolynomialKernel.evaluate,parameter,OcticPointing.cosineLoss]
  ring

theorem vector_bound (p : PointingCapPolynomial.Vector) {σ B : ℚ} (hp : bounded p σ B)
    (kind : Kind) {θ t : ℝ} (hθ : |θ|≤(σ:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖vectorValue p (parameter kind θ) t‖≤(B:ℝ) := by
  have hb (i : Fin 3) := bound_sound (p i) (parameter_bound kind hθ) ht
  have hbs (i : Fin 3) : (value (p i) (parameter kind θ) t)^2≤(bound (p i) (radius σ):ℝ)^2 := by
    have hi := hb i
    nlinarith [abs_nonneg (value (p i) (parameter kind θ) t),sq_abs (value (p i) (parameter kind θ) t)]
  have hB : (0:ℝ)≤B := by exact_mod_cast hp.1
  have hsB : (bound (p 0) (radius σ):ℝ)^2+(bound (p 1) (radius σ):ℝ)^2+
      (bound (p 2) (radius σ):ℝ)^2≤(B:ℝ)^2 := by exact_mod_cast hp.2
  have hn := pack_norm_sq (value (p 0) (parameter kind θ) t)
    (value (p 1) (parameter kind θ) t) (value (p 2) (parameter kind θ) t)
  change ‖vectorValue p (parameter kind θ) t‖^2=_ at hn
  nlinarith [hbs 0,hbs 1,hbs 2,norm_nonneg (vectorValue p (parameter kind θ) t)]

theorem reduced_residual (kind : Kind) (raw reduced witness : Coefficients)
    (h : zero (subtract raw (add reduced (multiply (constraint kind) witness))))
    (θ t : ℝ) : value raw (parameter kind θ) t=value reduced (parameter kind θ) t := by
  have he := identity raw (add reduced (multiply (constraint kind) witness)) h (parameter kind θ) t
  simpa only [value_add,value_multiply,value_constraint,zero_mul,add_zero] using he

end
end GNC.OrbitalComparison.VaryingRatePolynomial
