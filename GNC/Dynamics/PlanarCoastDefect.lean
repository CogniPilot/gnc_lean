import GNC.Analysis.PolynomialBounds
import GNC.Dynamics.PolynomialOrbit
import GNC.Dynamics.GravityLipschitz
import GNC.Dynamics.InverseRadius

/-! Rational certificates for a polynomial candidate of a planar Kepler
coast. A candidate is five rational time polynomials (position, velocity and
inverse radius) on a step of length `h`. Two executable rational quantities
are derived from the coefficients: a bound on the full-field acceleration
defect of the candidate, and a radius floor that turns into a Lipschitz
constant of the inverse-square field on a tube around the candidate. Both
are exactly the hypotheses consumed by the second-order comparison
certificate, so a rounded Taylor step becomes a proof once these rational
inequalities are checked.

The plane is `EuclideanSpace ℝ (Fin 2)` so that every norm is the Euclidean
norm of the gravity theorems. The true solution is written in the coordinate
form `Fin 4 → ℝ` of `PolynomialOrbit.physicalRate` and packed into the plane
componentwise; the packing changes no derivative.
-/
namespace GNC.PlanarCoast
open Set Planning.PolynomialKernel PolynomialBounds

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- Two real coordinates as a Euclidean plane vector. -/
def pack (a b : ℝ) : E2 := WithLp.toLp 2 ![a, b]

theorem pack_apply_zero (a b : ℝ) : pack a b 0 = a := rfl
theorem pack_apply_one (a b : ℝ) : pack a b 1 = b := rfl

theorem pack_add (a b c d : ℝ) : pack a b + pack c d = pack (a+c) (b+d) := by
  ext i; fin_cases i <;> simp [pack]

theorem pack_sub (a b c d : ℝ) : pack a b - pack c d = pack (a-c) (b-d) := by
  ext i; fin_cases i <;> simp [pack]

theorem pack_smul (r a b : ℝ) : r • pack a b = pack (r*a) (r*b) := by
  ext i; fin_cases i <;> simp [pack]

theorem pack_norm_sq (a b : ℝ) : ‖pack a b‖^2 = a^2+b^2 := by
  simp [pack, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

theorem pack_norm (a b : ℝ) : ‖pack a b‖ = Real.sqrt (a^2+b^2) := by
  rw [← pack_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The Euclidean norm is at most the sum of the coordinate magnitudes. -/
theorem pack_norm_le (a b : ℝ) : ‖pack a b‖ ≤ |a|+|b| := by
  have hsq := pack_norm_sq a b
  have hab : a^2+b^2 ≤ (|a|+|b|)^2 := by
    nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]
  have h : ‖pack a b‖^2 ≤ (|a|+|b|)^2 := hsq ▸ hab
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

theorem pack_hasDerivAt {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => pack (f s) (g s)) (pack f' g') t := by
  have hpi : HasDerivAt (fun s => ![f s, g s]) ![f', g'] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> simpa
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt t hpi

/-- The inverse-square field in packed coordinates. -/
theorem field_pack (a b : ℝ) :
    Gravity.field 1 (pack a b) =
      pack (-a/(Real.sqrt (a^2+b^2))^3) (-b/(Real.sqrt (a^2+b^2))^3) := by
  rw [Gravity.field, pack_norm, pack_smul]
  congr 1 <;> ring

/-! ### Rational polynomial evaluation and bounds -/

/-- Real evaluation of a rational coefficient list. -/
noncomputable def ev (cs : List ℚ) (t : ℝ) : ℝ := evaluate (cs.map (Rat.castHom ℝ)) t

theorem ev_nil (t : ℝ) : ev [] t = 0 := rfl

theorem ev_cons (a : ℚ) (rest : List ℚ) (t : ℝ) : ev (a :: rest) t = a+t*ev rest t := rfl

theorem ev_add (a b : List ℚ) (t : ℝ) : ev (add a b) t = ev a t+ev b t := by
  unfold ev; rw [add_map, evaluate_add]

theorem ev_subtract (a b : List ℚ) (t : ℝ) : ev (subtract a b) t = ev a t-ev b t := by
  unfold ev; rw [subtract_map, evaluate_subtract]

theorem ev_multiply (a b : List ℚ) (t : ℝ) : ev (multiply a b) t = ev a t*ev b t := by
  unfold ev; rw [multiply_map, evaluate_multiply]

theorem ev_hasDerivAt (cs : List ℚ) (t : ℝ) :
    HasDerivAt (ev cs) (ev (differentiate cs) t) t := by
  unfold ev
  rw [← differentiate_map]
  exact evaluate_hasDerivAt _ t

theorem ev_continuous (cs : List ℚ) : Continuous (ev cs) :=
  continuous_iff_continuousAt.mpr fun t => (ev_hasDerivAt cs t).continuousAt

theorem ev_abs_le (cs : List ℚ) {t : ℝ} {h : ℚ} (ht : |t| ≤ (h:ℝ)) :
    |ev cs t| ≤ (bound cs h : ℚ) := bound_sound cs ht

theorem bound_nonneg (cs : List ℚ) {h : ℚ} (hh : 0 ≤ h) : 0 ≤ bound cs h := by
  have hb := bound_sound cs (x := 0) (h := h) (by simpa using (show (0:ℝ) ≤ h by exact_mod_cast hh))
  exact_mod_cast (abs_nonneg _).trans hb

/-- Constant coefficient minus the absolute sum of the rest: a lower bound of
the polynomial on `[-h,h]`. -/
def lower : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: rest, h => a-h*bound rest h

theorem lower_le (cs : List ℚ) {t : ℝ} {h : ℚ} (ht : |t| ≤ (h:ℝ)) :
    ((lower cs h : ℚ) : ℝ) ≤ ev cs t := by
  cases cs with
  | nil => simp [lower, ev_nil]
  | cons a rest =>
    rw [ev_cons]
    have hb := ev_abs_le rest ht
    have hh : (0:ℝ) ≤ h := (abs_nonneg t).trans ht
    have hm : |t*ev rest t| ≤ h*bound rest h := by
      rw [abs_mul]
      exact mul_le_mul ht hb (abs_nonneg _) hh
    have := neg_abs_le (t*ev rest t)
    simp only [lower]
    push_cast
    linarith

/-! ### The candidate and its rational certificate data -/

/-- A polynomial candidate for one coast step: time polynomials for the
position, the velocity and the inverse radius on `[0,h]`, together with two
rational square-root witnesses for the radius range. -/
structure Candidate where
  x : List ℚ
  y : List ℚ
  vx : List ℚ
  vy : List ℚ
  u : List ℚ
  h : ℚ
  /-- A rational lower bound of the radius on the step. -/
  rhoMin : ℚ
  /-- A rational upper bound of the radius on the step. -/
  rhoMax : ℚ

namespace Candidate

def u3 (c : Candidate) : List ℚ := multiply c.u (multiply c.u c.u)

/-- Coefficients of `x''+u³x` and `y''+u³y`. -/
def resX (c : Candidate) : List ℚ := add (differentiate (differentiate c.x)) (multiply c.u3 c.x)
def resY (c : Candidate) : List ℚ := add (differentiate (differentiate c.y)) (multiply c.u3 c.y)

/-- Polynomial residual bound: `sup |q''+u³q|` on the step. -/
def residual (c : Candidate) : ℚ := bound c.resX c.h+bound c.resY c.h

/-- Coefficients of `x'-vx` and `y'-vy`. -/
def kinX (c : Candidate) : List ℚ := subtract (differentiate c.x) c.vx
def kinY (c : Candidate) : List ℚ := subtract (differentiate c.y) c.vy

/-- Kinematic defect bound: `sup |q'-v|` on the step. -/
def kinematic (c : Candidate) : ℚ := bound c.kinX c.h+bound c.kinY c.h

/-- Coefficients of the squared radius `x²+y²`. -/
def rho2 (c : Candidate) : List ℚ := add (multiply c.x c.x) (multiply c.y c.y)

/-- Coefficients of the inverse-radius residual `ρ²u²-1`. -/
def chiPoly (c : Candidate) : List ℚ := add (multiply c.rho2 (multiply c.u c.u)) [-1]

def chi (c : Candidate) : ℚ := bound c.chiPoly c.h
def rho2Min (c : Candidate) : ℚ := lower c.rho2 c.h
def rho2Max (c : Candidate) : ℚ := bound c.rho2 c.h
def uMin (c : Candidate) : ℚ := lower c.u c.h
def uMax (c : Candidate) : ℚ := bound c.u c.h
def zMax (c : Candidate) : ℚ := c.rhoMax*c.uMax
def zMin (c : Candidate) : ℚ := c.rhoMin*c.uMin

/-- Bound of `|q| |1/|q|³-u³|` through the inverse-radius identity. -/
def fieldError (c : Candidate) : ℚ :=
  c.chi/c.rho2Min*(1+c.zMax+c.zMax^2)/(1+c.zMin)

/-- Full-field acceleration defect bound of the candidate position polynomial. -/
def defect (c : Candidate) : ℚ := c.residual+c.fieldError

/-- The defect together with the kinematic defect. -/
def F (c : Candidate) : ℚ := c.defect+c.kinematic

/-- The rational inequalities that make the certificate data meaningful. -/
abbrev Valid (c : Candidate) : Prop :=
  0 ≤ c.h ∧ 0 < c.rho2Min ∧ 0 < c.uMin ∧ 0 ≤ c.rhoMin ∧ 0 ≤ c.rhoMax ∧
    c.rhoMin^2 ≤ c.rho2Min ∧ c.rho2Max ≤ c.rhoMax^2

/-! ### Real evaluation of the candidate -/

noncomputable def pos (c : Candidate) (t : ℝ) : E2 := pack (ev c.x t) (ev c.y t)

/-- Derivative of the position polynomial. -/
noncomputable def dpos (c : Candidate) (t : ℝ) : E2 :=
  pack (ev (differentiate c.x) t) (ev (differentiate c.y) t)

/-- The candidate's velocity polynomial. -/
noncomputable def vel (c : Candidate) (t : ℝ) : E2 := pack (ev c.vx t) (ev c.vy t)

/-- Second derivative of the position polynomial. -/
noncomputable def acc (c : Candidate) (t : ℝ) : E2 :=
  pack (ev (differentiate (differentiate c.x)) t) (ev (differentiate (differentiate c.y)) t)

noncomputable def invRadius (c : Candidate) (t : ℝ) : ℝ := ev c.u t

theorem pos_hasDerivAt (c : Candidate) (t : ℝ) : HasDerivAt c.pos (c.dpos t) t :=
  pack_hasDerivAt (ev_hasDerivAt c.x t) (ev_hasDerivAt c.y t)

theorem dpos_hasDerivAt (c : Candidate) (t : ℝ) : HasDerivAt c.dpos (c.acc t) t :=
  pack_hasDerivAt (ev_hasDerivAt _ t) (ev_hasDerivAt _ t)

theorem pos_continuous (c : Candidate) : Continuous c.pos :=
  continuous_iff_continuousAt.mpr fun t => (c.pos_hasDerivAt t).continuousAt

theorem dpos_continuous (c : Candidate) : Continuous c.dpos :=
  continuous_iff_continuousAt.mpr fun t => (c.dpos_hasDerivAt t).continuousAt

theorem step_abs {c : Candidate} {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) : |t| ≤ (c.h:ℝ) := by
  rw [abs_of_nonneg ht.1]; exact ht.2

theorem norm_pos_sq (c : Candidate) (t : ℝ) : ‖c.pos t‖^2 = ev c.rho2 t := by
  rw [pos, pack_norm_sq, rho2, ev_add, ev_multiply, ev_multiply]; ring

theorem rho2Min_le (c : Candidate) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    (c.rho2Min:ℝ) ≤ ‖c.pos t‖^2 := by
  rw [norm_pos_sq]; exact lower_le _ (step_abs ht)

theorem norm_pos_sq_le (c : Candidate) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    ‖c.pos t‖^2 ≤ (c.rho2Max:ℝ) := by
  rw [norm_pos_sq]; exact (le_abs_self _).trans (ev_abs_le _ (step_abs ht))

theorem rhoMin_le_norm_pos (c : Candidate) (hv : c.Valid) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    (c.rhoMin:ℝ) ≤ ‖c.pos t‖ := by
  have h1 : (c.rhoMin:ℝ)^2 ≤ c.rho2Min := by exact_mod_cast hv.2.2.2.2.2.1
  have h0 : (0:ℝ) ≤ c.rhoMin := by exact_mod_cast hv.2.2.2.1
  exact (pow_le_pow_iff_left₀ h0 (norm_nonneg _) two_ne_zero).mp
    (h1.trans (c.rho2Min_le ht))

theorem norm_pos_le_rhoMax (c : Candidate) (hv : c.Valid) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    ‖c.pos t‖ ≤ c.rhoMax := by
  have h1 : (c.rho2Max:ℝ) ≤ (c.rhoMax:ℝ)^2 := by exact_mod_cast hv.2.2.2.2.2.2
  have h0 : (0:ℝ) ≤ c.rhoMax := by exact_mod_cast hv.2.2.2.2.1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp
    ((c.norm_pos_sq_le ht).trans h1)

theorem norm_pos_pos (c : Candidate) (hv : c.Valid) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    0 < ‖c.pos t‖ := by
  have h : (0:ℝ) < c.rho2Min := by exact_mod_cast hv.2.1
  nlinarith [c.rho2Min_le ht, norm_nonneg (c.pos t)]

theorem uMin_le_invRadius (c : Candidate) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    (c.uMin:ℝ) ≤ c.invRadius t := lower_le _ (step_abs ht)

theorem invRadius_le_uMax (c : Candidate) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    c.invRadius t ≤ c.uMax := (le_abs_self _).trans (ev_abs_le _ (step_abs ht))

/-! ### Defect bounds -/

theorem residual_identity (c : Candidate) (t : ℝ) :
    c.acc t+(c.invRadius t)^3 • c.pos t = pack (ev c.resX t) (ev c.resY t) := by
  rw [acc, pos, pack_smul, pack_add, resX, resY, ev_add, ev_add, ev_multiply, ev_multiply,
    u3, ev_multiply, ev_multiply, invRadius]
  congr 1 <;> ring

/-- The polynomial residual `q''+u³q` is bounded by the coefficient sums. -/
theorem residual_bound (c : Candidate) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    ‖c.acc t+(c.invRadius t)^3 • c.pos t‖ ≤ c.residual := by
  rw [residual_identity]
  refine (pack_norm_le _ _).trans ?_
  have hx := ev_abs_le c.resX (step_abs ht)
  have hy := ev_abs_le c.resY (step_abs ht)
  unfold residual
  push_cast
  linarith

/-- The velocity polynomial differs from the position derivative by at most
the kinematic bound. -/
theorem kinematic_bound (c : Candidate) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    ‖c.dpos t-c.vel t‖ ≤ c.kinematic := by
  rw [dpos, vel, pack_sub]
  refine (pack_norm_le _ _).trans ?_
  have hx : |ev (differentiate c.x) t-ev c.vx t| ≤ (bound c.kinX c.h : ℚ) := by
    rw [← ev_subtract]; exact ev_abs_le _ (step_abs ht)
  have hy : |ev (differentiate c.y) t-ev c.vy t| ≤ (bound c.kinY c.h : ℚ) := by
    rw [← ev_subtract]; exact ev_abs_le _ (step_abs ht)
  unfold kinematic
  push_cast
  linarith

theorem chiPoly_eval (c : Candidate) (t : ℝ) :
    ev c.chiPoly t = ‖c.pos t‖^2*(c.invRadius t)^2-1 := by
  rw [chiPoly, ev_add, ev_multiply, ev_multiply, ← norm_pos_sq, ev_cons, ev_nil, invRadius]
  push_cast; ring

/-- The inverse-radius identity turns the residual `ρ²u²-1` into a bound of
the full inverse-cube error of the candidate. -/
theorem field_error_bound (c : Candidate) (hv : c.Valid) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    ‖Gravity.field 1 (c.pos t)+(c.invRadius t)^3 • c.pos t‖ ≤ c.fieldError := by
  set r := ‖c.pos t‖ with hr
  set u := c.invRadius t with hu
  have hrp : 0 < r := c.norm_pos_pos hv ht
  have huMin : (0:ℝ) < c.uMin := by exact_mod_cast hv.2.2.1
  have hu0 : 0 ≤ u := huMin.le.trans (c.uMin_le_invRadius ht)
  have hrho : (0:ℝ) < c.rho2Min := by exact_mod_cast hv.2.1
  have hrhoMin : (0:ℝ) ≤ c.rhoMin := by exact_mod_cast hv.2.2.2.1
  have he : Gravity.field 1 (c.pos t)+u^3 • c.pos t = (u^3-1/r^3) • c.pos t := by
    rw [Gravity.field, ← add_smul]; congr 1; ring
  rw [he, norm_smul, Real.norm_eq_abs, ← hr, Gravity.inverse_cube_defect hrp hu0]
  have hchi : |r^2*u^2-1| ≤ (c.chi:ℝ) := by
    rw [hr, hu, ← chiPoly_eval]; exact ev_abs_le _ (step_abs ht)
  have hz0 : 0 ≤ r*u := mul_nonneg hrp.le hu0
  have hzmax : r*u ≤ c.zMax := by
    rw [zMax]; push_cast
    exact mul_le_mul (c.norm_pos_le_rhoMax hv ht) (c.invRadius_le_uMax ht) hu0
      (by exact_mod_cast hv.2.2.2.2.1)
  have hzmin : (c.zMin:ℝ) ≤ r*u := by
    rw [zMin]; push_cast
    exact mul_le_mul (c.rhoMin_le_norm_pos hv ht) (c.uMin_le_invRadius ht) huMin.le hrp.le
  have hzmin0 : (0:ℝ) ≤ c.zMin := by
    rw [zMin]; push_cast; exact mul_nonneg hrhoMin huMin.le
  have hzmax0 : (0:ℝ) ≤ c.zMax := hz0.trans hzmax
  have hnum : (0:ℝ) ≤ 1+c.zMax+(c.zMax:ℝ)^2 := by nlinarith
  have hden : (0:ℝ) < 1+c.zMin := by linarith
  have hFz : (0:ℝ) ≤ (1+c.zMax+(c.zMax:ℝ)^2)/(1+c.zMin) := div_nonneg hnum hden.le
  have hfac : Gravity.inverseRadiusFactor (r*u) ≤ (1+c.zMax+(c.zMax:ℝ)^2)/(1+c.zMin) := by
    unfold Gravity.inverseRadiusFactor
    apply div_le_div₀ hnum (by nlinarith) (by positivity) (by linarith)
  have hdiv : Gravity.inverseRadiusFactor (r*u)/r^2 ≤
      (1+c.zMax+(c.zMax:ℝ)^2)/(1+c.zMin)/c.rho2Min :=
    div_le_div₀ hFz hfac hrho (c.rho2Min_le ht)
  have hfin := mul_le_mul hdiv hchi (abs_nonneg _) (div_nonneg hFz hrho.le)
  refine hfin.trans (le_of_eq ?_)
  unfold fieldError
  push_cast
  ring

/-- The full-field acceleration defect of the candidate on the step. -/
theorem defect_bound (c : Candidate) (hv : c.Valid) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    ‖c.acc t-Gravity.field 1 (c.pos t)‖ ≤ c.defect := by
  have he : c.acc t-Gravity.field 1 (c.pos t) =
      (c.acc t+(c.invRadius t)^3 • c.pos t)-
        (Gravity.field 1 (c.pos t)+(c.invRadius t)^3 • c.pos t) := by abel
  rw [he, defect]
  push_cast
  exact (norm_sub_le _ _).trans (add_le_add (c.residual_bound ht) (c.field_error_bound hv ht))

theorem defect_le_F (c : Candidate) (hv : c.Valid) : c.defect ≤ c.F := by
  unfold F kinematic
  linarith [bound_nonneg c.kinX hv.1, bound_nonneg c.kinY hv.1]

theorem defect_bound_F (c : Candidate) (hv : c.Valid) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) :
    ‖c.acc t-Gravity.field 1 (c.pos t)‖ ≤ c.F :=
  (c.defect_bound hv ht).trans (by exact_mod_cast c.defect_le_F hv)

/-! ### Lipschitz constant of the field on the tube -/

/-- On the tube of radius `M` around the candidate position the inverse-square
field is Lipschitz with constant `2/(ρmin-M)³`. -/
theorem field_lipschitz (c : Candidate) (hv : c.Valid) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h)
    {M : ℝ} (hM : M < c.rhoMin) (p p' : E2)
    (hp : ‖p-c.pos t‖ ≤ M) (hp' : ‖p'-c.pos t‖ ≤ M) :
    ‖Gravity.field 1 p-Gravity.field 1 p'‖ ≤ (2/((c.rhoMin:ℝ)-M)^3)*‖p-p'‖ := by
  have h := Gravity.field_difference_ball 1 (by norm_num) (c.pos t) (p-c.pos t) (p'-c.pos t)
    (r := (c.rhoMin:ℝ)-M) (R := M) (by linarith)
    (by linarith [c.rhoMin_le_norm_pos hv ht]) hp hp'
  simpa only [add_sub_cancel, sub_sub_sub_cancel_right, mul_one] using h

/-! ### The true solution and the error curve -/

/-- Position of a coordinate solution, packed into the plane. -/
noncomputable def truePos (w : ℝ → Fin 4 → ℝ) (t : ℝ) : E2 := pack (w t 0) (w t 1)

/-- Velocity of a coordinate solution, packed into the plane. -/
noncomputable def trueVel (w : ℝ → Fin 4 → ℝ) (t : ℝ) : E2 := pack (w t 2) (w t 3)

theorem truePos_hasDerivAt {w : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hw : HasDerivAt w (PolynomialOrbit.physicalRate 0 (w t)) t) :
    HasDerivAt (truePos w) (trueVel w t) t := by
  have h0 := hasDerivAt_pi.mp hw 0
  have h1 := hasDerivAt_pi.mp hw 1
  simp only [PolynomialOrbit.physicalRate, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact pack_hasDerivAt h0 h1

/-- The coordinate equations with zero thrust are the inverse-square field
in the plane. -/
theorem trueVel_hasDerivAt {w : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hw : HasDerivAt w (PolynomialOrbit.physicalRate 0 (w t)) t) :
    HasDerivAt (trueVel w) (Gravity.field 1 (truePos w t)) t := by
  have h2 := hasDerivAt_pi.mp hw 2
  have h3 := hasDerivAt_pi.mp hw 3
  simp only [PolynomialOrbit.physicalRate, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, zero_mul, zero_div, sub_zero, add_zero] at h2 h3
  rw [truePos, field_pack]
  exact pack_hasDerivAt h2 h3

theorem errorPos_hasDerivAt (c : Candidate) {w : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hw : HasDerivAt w (PolynomialOrbit.physicalRate 0 (w t)) t) :
    HasDerivAt (fun s => truePos w s-c.pos s) (trueVel w t-c.dpos t) t :=
  (truePos_hasDerivAt hw).sub (c.pos_hasDerivAt t)

theorem errorVel_hasDerivAt (c : Candidate) {w : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hw : HasDerivAt w (PolynomialOrbit.physicalRate 0 (w t)) t) :
    HasDerivAt (fun s => trueVel w s-c.dpos s)
      (Gravity.field 1 (truePos w t)-c.acc t) t :=
  (trueVel_hasDerivAt hw).sub (c.dpos_hasDerivAt t)

/-- The acceleration hypothesis of the second-order certificate: inside the
tube of radius `M` the error acceleration is bounded by the Lipschitz constant
times the position error plus the candidate defect. -/
theorem acceleration_hypothesis (c : Candidate) (hv : c.Valid)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h) {M : ℝ} (hM : M < c.rhoMin)
    (w : ℝ → Fin 4 → ℝ) (hp : ‖truePos w t-c.pos t‖ ≤ M) :
    ‖Gravity.field 1 (truePos w t)-c.acc t‖ ≤
      (2/((c.rhoMin:ℝ)-M)^3)*‖truePos w t-c.pos t‖+c.F := by
  have he : Gravity.field 1 (truePos w t)-c.acc t =
      (Gravity.field 1 (truePos w t)-Gravity.field 1 (c.pos t))+
        (Gravity.field 1 (c.pos t)-c.acc t) := by abel
  have hl := c.field_lipschitz hv ht hM (truePos w t) (c.pos t) hp
    (by rw [sub_self, norm_zero]; exact (norm_nonneg _).trans hp)
  have hd := c.defect_bound_F hv ht
  rw [norm_sub_rev] at hd
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hl hd)

/-- The candidate velocity polynomial is recovered from the position
derivative up to the kinematic bound. -/
theorem velocity_error_split (c : Candidate) {t : ℝ} (ht : t ∈ Icc (0:ℝ) c.h)
    (w : ℝ → Fin 4 → ℝ) :
    ‖trueVel w t-c.vel t‖ ≤ ‖trueVel w t-c.dpos t‖+c.kinematic := by
  have he : trueVel w t-c.vel t = (trueVel w t-c.dpos t)+(c.dpos t-c.vel t) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (c.kinematic_bound ht))

end Candidate

/-! ### An executable check -/

/-- A two-term candidate near perigee. -/
def sample : Candidate :=
  { x := [1, 0, -1/2], y := [0, 21/20], vx := [0, -1], vy := [21/20], u := [1],
    h := 1/10, rhoMin := 9/10, rhoMax := 11/10 }

example : sample.Valid := by decide +kernel

example : sample.F < 1 := by decide +kernel

end GNC.PlanarCoast
