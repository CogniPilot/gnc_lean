import GNC.Analysis.PolynomialBounds
import GNC.Lie.Euclidean

/-! Exact harmonic functions with polynomial envelopes.  The frequency is
never replaced by a time polynomial.  Rational coefficient and squared-norm
checks can therefore certify a candidate without resolving every input cycle.
This representation is equally available to a Cartesian construction. -/
namespace GNC.HarmonicPolynomial
open Real Set

abbrev Coeff := Fin 3 → Fin 2 → ℚ
abbrev Poly := List Coeff

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::add p q

def scale (a : ℚ) (p : Poly) : Poly := p.map (fun v i j => a*v i j)
def subtract (p q : Poly) : Poly := add p (scale (-1) q)

def weighted : ℕ → Poly → Poly
  | _, [] => []
  | n, a::p => (fun i j => (n:ℚ)*a i j)::weighted (n+1) p
def derivative (p : Poly) : Poly := weighted 1 p.tail

/-- Right multiplication by the exact planar harmonic generator. -/
def rate (ω : ℚ) (a : Coeff) : Coeff := fun i j =>
  if j = 0 then ω*a i 1 else -ω*a i 0

def squared (a : Coeff) : ℚ := ∑ i, ((a i 0)^2+(a i 1)^2)

abbrev Operator := Matrix (Fin 3) (Fin 3) ℚ
def mapCoeff (M : Operator) (a : Coeff) : Coeff := fun i j => ∑ k, M i k*a k j
def mapPoly (M : Operator) (p : Poly) : Poly := p.map (mapCoeff M)

def residual (D C : Operator) (p : Poly) (b : Coeff) : Poly :=
  subtract (subtract (subtract (derivative (derivative p)) (mapPoly D p))
    (mapPoly C (derivative p))) [b]

def fastResidual (D C : Operator) (ω : ℚ) (s b : Coeff) : Coeff :=
  mapCoeff D s+mapCoeff C (rate ω s)-rate ω (rate ω s)-b

noncomputable section
abbrev E3 := EuclideanSpace ℝ (Fin 3)

def column (a : Coeff) (j : Fin 2) : E3 := WithLp.toLp 2 (fun i => (a i j:ℝ))
def harmonic (a : Coeff) (θ : ℝ) : E3 :=
  cos θ • column a 0+sin θ • column a 1

def linear (M : Operator) : E3 →ₗ[ℝ] E3 := Matrix.toEuclideanLin (M.map (Rat.castHom ℝ))

def value : Poly → ℝ → ℝ → E3
  | [], _, _ => 0
  | a::p, t, θ => harmonic a θ+t • value p t θ

theorem harmonic_add (a b : Coeff) (θ : ℝ) :
    harmonic (a+b) θ = harmonic a θ+harmonic b θ := by
  ext i
  simp [harmonic,column]
  ring

theorem harmonic_scale (r : ℚ) (a : Coeff) (θ : ℝ) :
    harmonic (fun i j => r*a i j) θ = (r:ℝ) • harmonic a θ := by
  ext i
  simp [harmonic,column]
  ring

theorem harmonic_zero (θ : ℝ) : harmonic 0 θ = 0 := by
  ext i
  simp [harmonic,column]

theorem harmonic_subtract (a b : Coeff) (θ : ℝ) :
    harmonic (a-b) θ = harmonic a θ-harmonic b θ := by
  ext i
  simp [harmonic,column]
  ring

theorem harmonic_map (M : Operator) (a : Coeff) (θ : ℝ) :
    harmonic (mapCoeff M a) θ = linear M (harmonic a θ) := by
  have hc (j : Fin 2) : column (mapCoeff M a) j = linear M (column a j) := by
    ext i
    simp [column,linear,mapCoeff,Matrix.mulVec,dotProduct]
  simp only [harmonic,hc,map_add,map_smul]

theorem value_add (p q : Poly) (t θ : ℝ) :
    value (add p q) t θ = value p t θ+value q t θ := by
  induction p generalizing q with
  | nil => simp [add,value]
  | cons a p ih =>
    cases q with
    | nil => simp [add,value]
    | cons b q => simp only [add,value,harmonic_add,ih,smul_add]; abel

theorem value_scale (r : ℚ) (p : Poly) (t θ : ℝ) :
    value (scale r p) t θ = (r:ℝ) • value p t θ := by
  induction p with
  | nil => simp [scale,value]
  | cons a p ih =>
    simp only [scale,List.map_cons,value,harmonic_scale] at *
    rw [ih,smul_add,smul_smul,smul_smul,mul_comm t]

theorem value_subtract (p q : Poly) (t θ : ℝ) :
    value (subtract p q) t θ = value p t θ-value q t θ := by
  simp [subtract,value_add,value_scale,sub_eq_add_neg]

theorem value_map (M : Operator) (p : Poly) (t θ : ℝ) :
    value (mapPoly M p) t θ = linear M (value p t θ) := by
  induction p with
  | nil => simp [mapPoly,value]
  | cons a p ih =>
    simp only [mapPoly,List.map_cons,value,harmonic_map] at *
    rw [ih,map_add,map_smul]

theorem value_zero (p : Poly) (θ : ℝ) : value p 0 θ = harmonic (p.headD 0) θ := by
  cases p <;> simp [value,harmonic_zero]

theorem residual_value (D C : Operator) (p : Poly) (b : Coeff) (t θ : ℝ) :
    value (residual D C p b) t θ = value (derivative (derivative p)) t θ-
      linear D (value p t θ)-linear C (value (derivative p) t θ)-harmonic b θ := by
  simp [residual,value_subtract,value_map,value]

def response (p : Poly) (s : Coeff) (ω φ t : ℝ) : E3 :=
  value p t φ-harmonic s (ω*t+φ)

private theorem weighted_value (p : Poly) (n : ℕ) (t θ : ℝ) :
    value (weighted n p) t θ =
      (n:ℝ) • value p t θ+t • value (derivative p) t θ := by
  induction p generalizing n with
  | nil => simp [weighted,value,derivative]
  | cons a p ih =>
    simp only [weighted,value,harmonic_scale,Rat.cast_natCast]
    change (n:ℝ) • harmonic a θ+t • value (weighted (n+1) p) t θ =
      (n:ℝ) • (harmonic a θ+t • value p t θ)+
        t • value (weighted 1 p) t θ
    rw [ih,ih]
    push_cast
    module

theorem value_derivative (p : Poly) (t θ : ℝ) :
    HasDerivAt (fun s => value p s θ) (value (derivative p) t θ) t := by
  induction p with
  | nil => simpa [value,derivative,weighted] using (hasDerivAt_const t (0:E3))
  | cons a p ih =>
    have h := (hasDerivAt_const t (harmonic a θ)).add ((hasDerivAt_id t).smul ih)
    convert h using 1
    simpa only [derivative,List.tail_cons,Nat.cast_one,one_smul,zero_add,id_eq,add_comm] using
      weighted_value p 1 t θ

theorem harmonic_derivative (a : Coeff) (ω φ t : ℝ) (w : ℚ) (hw : (w:ℝ)=ω) :
    HasDerivAt (fun s => harmonic a (ω*s+φ)) (harmonic (rate w a) (ω*t+φ)) t := by
  have hθ := ((hasDerivAt_id t).const_mul ω).add_const φ
  have h := (hθ.cos.smul_const (column a 0)).add (hθ.sin.smul_const (column a 1))
  convert h using 1
  ext i
  simp [harmonic,column,rate,hw]
  ring

theorem response_derivative (p : Poly) (s : Coeff) (ω : ℚ) (φ t : ℝ) :
    HasDerivAt (response p s (ω:ℝ) φ)
      (response (derivative p) (rate ω s) (ω:ℝ) φ t) t :=
  (value_derivative p t φ).sub (harmonic_derivative s (ω:ℝ) φ t ω rfl)

theorem response_initial (p : Poly) (s : Coeff) (ω : ℚ) (φ : ℝ)
    (hp : p.headD 0 = s) (hv : (derivative p).headD 0 = rate ω s) :
    response p s (ω:ℝ) φ 0 = 0 ∧
      response (derivative p) (rate ω s) (ω:ℝ) φ 0 = 0 := by
  simp only [response,value_zero,hp,hv,mul_zero,zero_add,sub_self,and_self]

theorem response_residual (D C : Operator) (p : Poly) (s b₀ b : Coeff)
    (ω : ℚ) (φ t : ℝ) :
    response (derivative (derivative p)) (rate ω (rate ω s)) (ω:ℝ) φ t-
      linear D (response p s (ω:ℝ) φ t)-
      linear C (response (derivative p) (rate ω s) (ω:ℝ) φ t)-
      harmonic b₀ φ-
      harmonic b ((ω:ℝ)*t+φ) =
    value (residual D C p b₀) t φ+
      harmonic (fastResidual D C ω s b) ((ω:ℝ)*t+φ) := by
  simp only [response,residual_value,fastResidual,harmonic_add,
    harmonic_subtract,harmonic_map,harmonic_zero,map_sub,sub_zero]
  abel

/-- A rational squared Frobenius bound is valid for every phase.  The two
columns retain the unit-circle dependency rather than becoming a box. -/
theorem harmonic_bound (a : Coeff) {r : ℚ} (hr : 0 ≤ r)
    (ha : squared a ≤ r^2) (θ : ℝ) : ‖harmonic a θ‖ ≤ (r:ℝ) := by
  have hc := norm_add_le (cos θ • column a 0) (sin θ • column a 1)
  simp only [norm_smul,Real.norm_eq_abs] at hc
  have hsq : ‖column a 0‖^2+‖column a 1‖^2 ≤ (r:ℝ)^2 := by
    have h : (squared a:ℝ) ≤ (r:ℝ)^2 := by exact_mod_cast ha
    simpa [squared,column,EuclideanSpace.real_norm_sq_eq,Finset.sum_add_distrib] using h
  have he := sin_sq_add_cos_sq θ
  have hcs := sq_nonneg (|cos θ| * ‖column a 1‖-|sin θ| * ‖column a 0‖)
  have hp : 0 ≤ |cos θ| * ‖column a 0‖+|sin θ| * ‖column a 1‖ := by positivity
  have hid : (|cos θ| * ‖column a 0‖+|sin θ| * ‖column a 1‖)^2+
      (|cos θ| * ‖column a 1‖-|sin θ| * ‖column a 0‖)^2 =
      ‖column a 0‖^2+‖column a 1‖^2 := by
    calc
      _ = (|sin θ|^2+|cos θ|^2)*(‖column a 0‖^2+‖column a 1‖^2) := by ring
      _ = _ := by rw [sq_abs,sq_abs,he,one_mul]
  have hsquare : (|cos θ| * ‖column a 0‖+|sin θ| * ‖column a 1‖)^2 ≤ (r:ℝ)^2 := by
    nlinarith
  have hrR : (0:ℝ) ≤ r := by exact_mod_cast hr
  exact (show ‖harmonic a θ‖ ≤ _ from hc).trans (by nlinarith)

def Bounds : Poly → List ℚ → Prop
  | [], [] => True
  | a::p, r::rs => 0 ≤ r ∧ squared a ≤ r^2 ∧ Bounds p rs
  | _, _ => False

instance (p : Poly) (rs : List ℚ) : Decidable (Bounds p rs) := by
  induction p generalizing rs with
  | nil => cases rs <;> simp only [Bounds] <;> infer_instance
  | cons a p ih => cases rs <;> simp only [Bounds] <;> infer_instance

theorem value_bound (p : Poly) (rs : List ℚ) (h : Bounds p rs)
    {t : ℝ} (ht : |t| ≤ 1) (θ : ℝ) : ‖value p t θ‖ ≤ (rs.sum:ℝ) := by
  induction p generalizing rs with
  | nil => cases rs <;> simp_all [Bounds,value]
  | cons a p ih =>
    cases rs with
    | nil => simp [Bounds] at h
    | cons r rs =>
      rcases h with ⟨hr,ha,hp⟩
      have hb := ih rs hp
      have hn := norm_smul t (value p t θ)
      have hh := (norm_add_le (harmonic a θ) (t • value p t θ)).trans
        (add_le_add (harmonic_bound a hr ha θ)
          (show ‖t • value p t θ‖ ≤ (rs.sum:ℝ) from by
            rw [hn,Real.norm_eq_abs]
            exact (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans (by simpa using hb)))
      simpa [value,List.sum_cons] using hh

theorem response_residual_bound (D C : Operator) (p : Poly) (s b₀ b : Coeff)
    (ω : ℚ) (rs : List ℚ) (h : Bounds (residual D C p b₀) rs)
    {r : ℚ} (hr : 0 ≤ r) (hb : squared (fastResidual D C ω s b) ≤ r^2)
    {t : ℝ} (ht : |t| ≤ 1) (φ : ℝ) :
    ‖response (derivative (derivative p)) (rate ω (rate ω s)) (ω:ℝ) φ t-
      linear D (response p s (ω:ℝ) φ t)-
      linear C (response (derivative p) (rate ω s) (ω:ℝ) φ t)-
      harmonic b₀ φ-
      harmonic b ((ω:ℝ)*t+φ)‖ ≤ ((rs.sum+r:ℚ):ℝ) := by
  rw [response_residual]
  exact (norm_add_le _ _).trans (by
    simpa using add_le_add (value_bound _ rs h ht φ) (harmonic_bound _ hr hb _))

theorem response_bound (p : Poly) (s : Coeff) (ω φ : ℝ)
    (rs : List ℚ) (h : Bounds p rs) {r : ℚ} (hr : 0 ≤ r)
    (hs : squared s ≤ r^2) {t : ℝ} (ht : |t| ≤ 1) :
    ‖response p s ω φ t‖ ≤ ((rs.sum+r:ℚ):ℝ) := by
  exact (norm_sub_le _ _).trans (by
    simpa using add_le_add (value_bound p rs h ht φ) (harmonic_bound s hr hs (ω*t+φ)))

theorem response_continuous (p : Poly) (s : Coeff) (ω : ℚ) (φ : ℝ) :
    Continuous (response p s (ω:ℝ) φ) :=
  continuous_iff_continuousAt.mpr fun t => (response_derivative p s ω φ t).continuousAt

end
end GNC.HarmonicPolynomial
