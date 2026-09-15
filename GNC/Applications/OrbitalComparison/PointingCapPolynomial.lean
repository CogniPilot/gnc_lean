import GNC.Applications.OrbitalComparison.PointingCapBurn
import GNC.Analysis.ParameterPolynomial
import GNC.Analysis.RadialSourceCertificate

/-! Executable coefficient checks for the two-direction pointing family.
The generator may propose any coefficients and a sphere-reduction witness.
Exact polynomial identities and bounds establish the accepted semantics. -/
namespace GNC.OrbitalComparison.PointingCapPolynomial
open ParameterPolynomial
open SpatialBurn PointingCapBurn Set

def u : Coefficients := [⟨1,0,0,[1]⟩]
def v : Coefficients := [⟨0,1,0,[1]⟩]
def c : Coefficients := [⟨0,0,1,[1]⟩]
def transverse : Coefficients := add (multiply u u) (multiply v v)
def constraint : Coefficients := add (subtract (multiply c c) (scale 2 c)) transverse
def radial : List ℚ → Coefficients
  | [] => []
  | a::p => add (constant a) (multiply transverse (radial p))

def source (p : Option (List ℚ)) : Coefficients :=
  match p with | none => c | some p => radial p
/-- Sixteen fixed subintervals bound the scalar source residual. This only
refines a known polynomial range; it does not iterate the physical tube. -/
def sourceError (p : Option (List ℚ)) (σ : ℚ) : ℚ :=
  match p with | none => 0 | some p => RadialSourceCertificate.refinedError 4 p (σ^2)
def SourceValid (p : Option (List ℚ)) (σ : ℚ) : Prop :=
  match p with | none => True | some p => RadialSourceCertificate.Valid p (σ^2)
instance (p : Option (List ℚ)) (σ : ℚ) : Decidable (SourceValid p σ) := by
  cases p <;> unfold SourceValid <;> infer_instance

def radius (σ : ℚ) : Fin 3 → ℚ := ![σ,σ,σ^2/(2-σ^2)]
abbrev Vector := Fin 3 → Coefficients
def derivative (p : Vector) : Vector := fun i => ParameterPolynomial.derivative (p i)
def difference (p q : Vector) : Vector := fun i => subtract (p i) (q i)
def bounded (p : Vector) (σ B : ℚ) : Prop :=
  0≤B ∧ (bound (p 0) (radius σ))^2+(bound (p 1) (radius σ))^2+
    (bound (p 2) (radius σ))^2≤B^2
instance (p : Vector) (σ B : ℚ) : Decidable (bounded p σ B) := by unfold bounded; infer_instance
def initialZero (p : Coefficients) : Prop := ∀ a ∈ p, a.time.headD 0=0
instance (p : Coefficients) : Decidable (initialZero p) := by unfold initialZero; infer_instance

noncomputable section

@[simp] theorem value_u (x : Fin 3 → ℝ) (t : ℝ) : value u x t=x 0 := by
  simp [u,value,termValue,monomial,PolynomialOrder.value,Planning.PolynomialKernel.evaluate]
@[simp] theorem value_v (x : Fin 3 → ℝ) (t : ℝ) : value v x t=x 1 := by
  simp [v,value,termValue,monomial,PolynomialOrder.value,Planning.PolynomialKernel.evaluate]
@[simp] theorem value_c (x : Fin 3 → ℝ) (t : ℝ) : value c x t=x 2 := by
  simp [c,value,termValue,monomial,PolynomialOrder.value,Planning.PolynomialKernel.evaluate]
theorem value_transverse (x : Fin 3 → ℝ) (t : ℝ) : value transverse x t=x 0^2+x 1^2 := by
  simp [transverse,value_add,value_multiply,pow_two]
theorem value_constraint {σ : ℝ} {x : Fin 3 → ℝ} (hx : Admissible σ x) (t : ℝ) :
    value constraint x t=0 := by
  simp only [constraint,value_add,value_subtract,value_multiply,value_scale,value_c,value_transverse]
  norm_num only [Rat.cast_ofNat]
  nlinarith [hx.2.2.1]
theorem value_radial (p : List ℚ) (x : Fin 3 → ℝ) (t : ℝ) :
    value (radial p) x t=PolynomialOrder.value p (x 0^2+x 1^2) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [radial,value_add,value_constant,value_multiply,value_transverse,ih]
    rfl

theorem source_error (p : Option (List ℚ)) (σ : ℚ) (hv : SourceValid p σ)
    {x : Fin 3 → ℝ} (hx : Admissible (σ:ℝ) x) (t : ℝ) :
    |x 2-value (source p) x t|≤(sourceError p σ:ℝ) := by
  cases p with
  | none => simp [source,sourceError]
  | some p =>
    simp only [source,sourceError,value_radial]
    apply RadialSourceCertificate.refined_certifies 4 p (σ^2) hv _ _ _ hx.1 hx.2.1 hx.2.2.1
    simpa only [Rat.cast_pow] using hx.2.2.2

def vectorValue (p : Vector) (x : Fin 3 → ℝ) (t : ℝ) : E3 :=
  pack (value (p 0) x t) (value (p 1) x t) (value (p 2) x t)

theorem vector_derivative (p : Vector) (x : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (vectorValue p x) (vectorValue (derivative p) x t) t := by
  simpa only [vectorValue,pack,derivative] using
    (((value_derivative (p 0) x t).smul_const e0).add
      ((value_derivative (p 1) x t).smul_const e1)).add
      ((value_derivative (p 2) x t).smul_const e2)

theorem vector_difference (p q : Vector) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue (difference p q) x t=vectorValue p x t-vectorValue q x t := by
  simp only [vectorValue,difference,value_subtract,pack]
  module

theorem vector_bound (p : Vector) {σ B : ℚ} (hσ : 0≤σ) (hs : σ^2<1)
    (hp : bounded p σ B) {x : Fin 3 → ℝ} (hx : Admissible (σ:ℝ) x)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖vectorValue p x t‖≤(B:ℝ) := by
  have hr := parameter_bounds (show (0:ℝ)≤σ by exact_mod_cast hσ)
    (show (σ:ℝ)^2<1 by exact_mod_cast hs) hx
  have hpar (i : Fin 3) : |x i|≤(radius σ i:ℝ) := by
    fin_cases i
    · simpa [radius] using hr.1
    · simpa [radius] using hr.2.1
    · simpa [radius] using hr.2.2
  have hb (i : Fin 3) := bound_sound (p i) hpar ht
  have hbs (i : Fin 3) : (value (p i) x t)^2≤(bound (p i) (radius σ):ℝ)^2 := by
    have hi := hb i
    nlinarith [abs_nonneg (value (p i) x t),sq_abs (value (p i) x t)]
  have hB : (0:ℝ)≤B := by exact_mod_cast hp.1
  have hsB : (bound (p 0) (radius σ):ℝ)^2+(bound (p 1) (radius σ):ℝ)^2+
      (bound (p 2) (radius σ):ℝ)^2≤(B:ℝ)^2 := by exact_mod_cast hp.2
  have hn := pack_norm_sq (value (p 0) x t) (value (p 1) x t) (value (p 2) x t)
  change ‖vectorValue p x t‖^2=_ at hn
  nlinarith [hbs 0,hbs 1,hbs 2,norm_nonneg (vectorValue p x t)]

theorem initial_value (p : Coefficients) (hp : initialZero p) (x : Fin 3 → ℝ) :
    value p x 0=0 := by
  have h0 (a : List ℚ) : PolynomialOrder.value a 0=(a.headD 0:ℝ) := by
    cases a <;> simp [PolynomialOrder.value,Planning.PolynomialKernel.evaluate]
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha := hp a (by simp)
    rw [value_cons,ih (fun b hb => hp b (by simp [hb]))]
    simp only [termValue,h0,ha,Rat.cast_zero,zero_mul,add_zero]

theorem reduced_residual (raw reduced witness : Coefficients)
    (h : zero (subtract raw (add reduced (multiply constraint witness))))
    {σ : ℝ} {x : Fin 3 → ℝ} (hx : Admissible σ x) (t : ℝ) :
    value raw x t=value reduced x t := by
  have he := identity raw (add reduced (multiply constraint witness)) h x t
  simpa only [value_add,value_multiply,value_constraint hx,zero_mul,add_zero] using he

end
end GNC.OrbitalComparison.PointingCapPolynomial
