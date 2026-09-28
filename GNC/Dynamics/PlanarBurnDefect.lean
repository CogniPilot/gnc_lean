import GNC.Dynamics.PlanarCoastCurvature
import GNC.Dynamics.OrbitEnclosure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Rational certificates for a fixed-thrust planar burn with mass depletion
and thrust misalignment. On top of the coast defect and curvature certificates
of `PlanarCoastDefect` and `PlanarCoastCurvature`, this module adds a
polynomial candidate for the reciprocal mass `w = 1/(m₀ - σ t)`, a polynomial
first-order misalignment sensitivity `ĝ = (ĝ_p, ĝ_v)`, and the linearized error
dynamics of a true burn trajectory about the segment `x̂ + δ ĝ` swept by the
misalignment angle `δ`.

The physical model (normalized gravitational parameter one) is planar,
`q'' = g(q) + f w(t) R(δ) e`, with `g(q) = -q/‖q‖³`, constant nominal thrust
direction `e` a rational unit vector, `R(δ)` the planar rotation by the
misalignment `|δ| ≤ α`, `w(t) = 1/(m₀ - s t)` the reciprocal mass on a step
that starts at mass `m₀`, and `f`, `s` rational thrust and mass-rate
parameters with `s h < m₀` on the step. Coast is the case `f = 0`, where the
dynamics reduce to `PolynomialOrbit.physicalRate 0`.

All rational certificate quantities are absolute coefficient sums, so a finite
rational check certifies a real inequality on the whole step, and the error
dynamics are packed into the `EuclideanSpace ℝ (Fin 4)` state used by the
transported certificate, with `n(t)` supported on the velocity block. -/
noncomputable section
open Set Matrix
open scoped RealInnerProductSpace
namespace GNC.PlanarBurn
open GNC.PlanarCoast Planning.PolynomialKernel PolynomialBounds

/-! ### Scalar trigonometric remainders for the misalignment chord -/

/-- The chord defect of `cos`: `1 - cos x ≤ x²/2`. -/
theorem one_sub_cos_le (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

/-- `s ↦ x³/6 - x + sin x` is monotone, since its derivative
`x²/2 - 1 + cos x` is nonnegative by the `cos` chord bound. -/
theorem monotone_cube_sub_sin :
    Monotone (fun x : ℝ => x ^ 3 / 6 - x + Real.sin x) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => x ^ 3 / 6 - x + Real.sin x)
        (x ^ 2 / 2 - 1 + Real.cos x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x ^ 3 / 6) (x ^ 2 / 2) x := by
      have h := (hasDerivAt_pow 3 x).div_const 6
      convert h using 1; push_cast; ring
    have h2 : HasDerivAt (fun x : ℝ => x) (1 : ℝ) x := hasDerivAt_id x
    have h3 : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x
    exact (h1.sub h2).add h3
  refine monotone_of_deriv_nonneg ?_ ?_
  · exact fun x => (hderiv x).differentiableAt
  · intro x
    rw [(hderiv x).deriv]
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

/-- `s ↦ x - sin x` is monotone, since its derivative `1 - cos x` is
nonnegative. -/
theorem monotone_sub_sin : Monotone (fun x : ℝ => x - Real.sin x) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => x - Real.sin x) (1 - Real.cos x) x := by
    intro x
    exact (hasDerivAt_id x).sub (Real.hasDerivAt_sin x)
  refine monotone_of_deriv_nonneg ?_ ?_
  · exact fun x => (hderiv x).differentiableAt
  · intro x
    rw [(hderiv x).deriv]
    linarith [Real.cos_le_one x]

/-- The chord defect of `sin`: `|x - sin x| ≤ |x|³/6`, for every real `x`. -/
theorem abs_sub_sin_le (x : ℝ) : |x - Real.sin x| ≤ |x| ^ 3 / 6 := by
  have key : ∀ y : ℝ, 0 ≤ y → 0 ≤ y - Real.sin y ∧ y - Real.sin y ≤ y ^ 3 / 6 := by
    intro y hy
    constructor
    · have h := monotone_sub_sin hy
      simpa using h
    · have h := monotone_cube_sub_sin hy
      simp only at h
      have h0 : (0 : ℝ) ^ 3 / 6 - 0 + Real.sin 0 = 0 := by simp
      have := h0 ▸ h
      linarith
  rcases le_total 0 x with hx | hx
  · obtain ⟨h0, h1⟩ := key x hx
    rw [abs_of_nonneg h0, abs_of_nonneg hx]
    exact h1
  · have hnx : 0 ≤ -x := by linarith
    obtain ⟨h0, h1⟩ := key (-x) hnx
    have hle : x - Real.sin x ≤ 0 := by rw [Real.sin_neg] at h0; linarith
    rw [abs_of_nonpos hle, abs_of_nonpos hx]
    rw [show -(x - Real.sin x) = (-x) - Real.sin (-x) by rw [Real.sin_neg]; ring]
    exact h1

/-! ### Small geometric helpers on the packed state -/

/-- The position block of a stacked state is no larger than the whole state. -/
theorem norm_le_join2_left (x y : E2) : ‖x‖ ≤ ‖join2 x y‖ := by
  have h : ‖x‖ ^ 2 ≤ ‖join2 x y‖ ^ 2 := by
    rw [join2_norm_sq]; nlinarith [norm_nonneg y]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The matrix action is additive in the vector argument. -/
theorem act_vsub {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (a b : EuclideanSpace ℝ (Fin n)) :
    act M (a - b) = act M a - act M b := by
  simp only [act, map_sub]

/-- The matrix action commutes with real scaling of the vector argument. -/
theorem act_vsmul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (a : EuclideanSpace ℝ (Fin n)) : act M (r • a) = r • act M a := by
  simp only [act, map_smul]

/-- The Frobenius norm is symmetric under sign of the difference. -/
theorem frob_sub_comm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    frob (A - B) = frob (B - A) := by
  unfold frob
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.sub_apply, Matrix.sub_apply]; ring

/-! ### The burn candidate -/

/-- A polynomial certificate for one burn step. On top of the coast candidate
(`x y vx vy u`, the step length `h` and the radius range) it carries a
reciprocal-mass polynomial `wPoly`, a first-order misalignment sensitivity
`(gx gy, gvx gvy)`, the rational thrust and mass-rate parameters `f`, `s`, the
step-start mass `m0`, the rational unit thrust direction `(ex, ey)` and the
misalignment bound `alpha`. -/
structure BurnCandidate extends Candidate where
  /-- Reciprocal-mass candidate `ŵ`. -/
  wPoly : List ℚ
  /-- Sensitivity position candidate components `ĝ_p = (gx, gy)`. -/
  gx : List ℚ
  gy : List ℚ
  /-- Sensitivity velocity candidate components `ĝ_v = (gvx, gvy)`. -/
  gvx : List ℚ
  gvy : List ℚ
  /-- Thrust parameter `f = F/(m_i a*)`. -/
  f : ℚ
  /-- Mass-rate parameter `s = σ t*/m_i`. -/
  s : ℚ
  /-- Mass at the step start. -/
  m0 : ℚ
  /-- Nominal thrust direction (a rational unit vector). -/
  ex : ℚ
  ey : ℚ
  /-- Misalignment magnitude bound. -/
  alpha : ℚ

namespace BurnCandidate

/-! ### Real-valued data attached to a burn candidate -/

/-- The true reciprocal mass `w(t) = 1/(m₀ - s t)`. -/
def wReal (bc : BurnCandidate) (t : ℝ) : ℝ := 1 / ((bc.m0 : ℝ) - (bc.s : ℝ) * t)

/-- The nominal thrust direction as a plane vector. -/
def edir (bc : BurnCandidate) : E2 := pack (bc.ex : ℝ) (bc.ey : ℝ)

/-- The quarter-turn `J e = (-e₂, e₁)` of the nominal direction. -/
def Jdir (bc : BurnCandidate) : E2 := pack (-(bc.ey : ℝ)) (bc.ex : ℝ)

/-- The misaligned direction `R(δ) e`. -/
def rotDir (bc : BurnCandidate) (δ : ℝ) : E2 :=
  pack ((bc.ex : ℝ) * Real.cos δ - (bc.ey : ℝ) * Real.sin δ)
    ((bc.ex : ℝ) * Real.sin δ + (bc.ey : ℝ) * Real.cos δ)

/-- The thrust acceleration `f w(t) R(δ) e`. -/
def thrustAcc (bc : BurnCandidate) (δ t : ℝ) : E2 :=
  ((bc.f : ℝ) * wReal bc t) • rotDir bc δ

/-- The sensitivity position candidate `ĝ_p`. -/
def gp (bc : BurnCandidate) (t : ℝ) : E2 := pack (ev bc.gx t) (ev bc.gy t)

/-- The sensitivity velocity candidate `ĝ_v`. -/
def gv (bc : BurnCandidate) (t : ℝ) : E2 := pack (ev bc.gvx t) (ev bc.gvy t)

/-- The derivative of the sensitivity position candidate `ĝ_p'`. -/
def dgp (bc : BurnCandidate) (t : ℝ) : E2 :=
  pack (ev (differentiate bc.gx) t) (ev (differentiate bc.gy) t)

/-- The derivative of the sensitivity velocity candidate `ĝ_v'`. -/
def dgv (bc : BurnCandidate) (t : ℝ) : E2 :=
  pack (ev (differentiate bc.gvx) t) (ev (differentiate bc.gvy) t)

theorem gp_hasDerivAt (bc : BurnCandidate) (t : ℝ) : HasDerivAt bc.gp (bc.dgp t) t :=
  pack_hasDerivAt (ev_hasDerivAt _ t) (ev_hasDerivAt _ t)

theorem gv_hasDerivAt (bc : BurnCandidate) (t : ℝ) : HasDerivAt bc.gv (bc.dgv t) t :=
  pack_hasDerivAt (ev_hasDerivAt _ t) (ev_hasDerivAt _ t)

/-! ### Rational certificate data -/

/-- The step denominator `m₀ - s h`; positive on a valid step. -/
def sDenom (bc : BurnCandidate) : ℚ := bc.m0 - bc.s * bc.h

/-- The reciprocal-mass residual polynomial `ŵ (m₀ - s t) - 1`. -/
def chiWPoly (bc : BurnCandidate) : List ℚ :=
  subtract (multiply bc.wPoly [bc.m0, -bc.s]) [1]

/-- Bound of `|ŵ (m₀ - s t) - 1|` on the step. -/
def chiW (bc : BurnCandidate) : ℚ := bound bc.chiWPoly bc.h

/-- Bound of `sup w` on the step. -/
def wMax (bc : BurnCandidate) : ℚ := bound bc.wPoly bc.h + bc.chiW / bc.sDenom

/-- Bound of `sup ‖ĝ_p‖` on the step. -/
def Gp (bc : BurnCandidate) : ℚ := bound bc.gx bc.h + bound bc.gy bc.h

/-- Bound of `sup ‖ĝ_v‖` on the step. -/
def Gv (bc : BurnCandidate) : ℚ := bound bc.gvx bc.h + bound bc.gvy bc.h

/-- Coefficients of `x'' + û³ x - f ŵ eₓ` and `y'' + û³ y - f ŵ e_y`. -/
def resNomXc (bc : BurnCandidate) : List ℚ :=
  subtract bc.toCandidate.resX (scale (bc.f * bc.ex) bc.wPoly)
def resNomYc (bc : BurnCandidate) : List ℚ :=
  subtract bc.toCandidate.resY (scale (bc.f * bc.ey) bc.wPoly)

/-- Polynomial residual bound of the nominal thrust equation. -/
def resNom (bc : BurnCandidate) : ℚ := bound bc.resNomXc bc.h + bound bc.resNomYc bc.h

/-- The fifth power of the inverse-radius candidate as a polynomial. -/
def u5 (bc : BurnCandidate) : List ℚ := multiply bc.toCandidate.u3 (multiply bc.u bc.u)

/-- Entries of the lower block `B̂ = -û³ I + 3 û⁵ q̂ q̂ᵀ`. -/
def bxx (bc : BurnCandidate) : List ℚ :=
  subtract (scale 3 (multiply bc.u5 (multiply bc.x bc.x))) bc.toCandidate.u3
def bxy (bc : BurnCandidate) : List ℚ := scale 3 (multiply bc.u5 (multiply bc.x bc.y))
def byx (bc : BurnCandidate) : List ℚ := scale 3 (multiply bc.u5 (multiply bc.y bc.x))
def byy (bc : BurnCandidate) : List ℚ :=
  subtract (scale 3 (multiply bc.u5 (multiply bc.y bc.y))) bc.toCandidate.u3

/-- Coefficients of the two components of `B̂ ĝ_p`. -/
def BxPoly (bc : BurnCandidate) : List ℚ := add (multiply bc.bxx bc.gx) (multiply bc.bxy bc.gy)
def ByPoly (bc : BurnCandidate) : List ℚ := add (multiply bc.byx bc.gx) (multiply bc.byy bc.gy)

/-- Coefficients of the sensitivity residual `ĝ_v' - B̂ ĝ_p - f ŵ J e`. -/
def resSensXc (bc : BurnCandidate) : List ℚ :=
  subtract (subtract (differentiate bc.gvx) bc.BxPoly) (scale (bc.f * (-bc.ey)) bc.wPoly)
def resSensYc (bc : BurnCandidate) : List ℚ :=
  subtract (subtract (differentiate bc.gvy) bc.ByPoly) (scale (bc.f * bc.ex) bc.wPoly)

/-- Polynomial residual bound of the sensitivity equation. -/
def resG (bc : BurnCandidate) : ℚ := bound bc.resSensXc bc.h + bound bc.resSensYc bc.h

/-- Nominal thrust defect bound `Fx`. -/
def Fx (bc : BurnCandidate) : ℚ :=
  bc.resNom + bc.toCandidate.fieldError + bc.f * bc.chiW / bc.sDenom

/-- Sensitivity defect bound `Fg`. -/
def Fg (bc : BurnCandidate) : ℚ :=
  bc.resG + GNC.PlanarCoast.epsA bc.toCandidate * bc.Gp + bc.f * bc.chiW / bc.sDenom

/-- Misalignment defect bound `Fmis`. -/
def Fmis (bc : BurnCandidate) : ℚ := bc.f * bc.wMax * (bc.alpha ^ 2 / 2 + bc.alpha ^ 3 / 6)

/-- The decidable rational hypotheses of the burn certificate. -/
def Valid (bc : BurnCandidate) : Prop :=
  bc.toCandidate.Valid ∧ 0 < bc.rhoMin ∧ 0 ≤ bc.f ∧ 0 ≤ bc.s ∧ 0 < bc.sDenom ∧
    0 ≤ bc.alpha ∧ bc.ex ^ 2 + bc.ey ^ 2 = 1 ∧
    bc.gvx = differentiate bc.gx ∧ bc.gvy = differentiate bc.gy

instance (bc : BurnCandidate) : Decidable bc.Valid := by unfold Valid; infer_instance

/-! ### Evaluation helpers -/

theorem ev_scale (q : ℚ) (p : List ℚ) (t : ℝ) : ev (scale q p) t = (q : ℝ) * ev p t := by
  unfold ev; rw [scale_map, evaluate_scale]; simp

section Sound
variable (bc : BurnCandidate) (hv : bc.Valid)
include hv

theorem sDenom_pos : (0 : ℝ) < (bc.sDenom : ℝ) := by exact_mod_cast hv.2.2.2.2.1

/-- The reciprocal mass has positive denominator on the step. -/
theorem wDenom_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) bc.h) :
    (0 : ℝ) < (bc.m0 : ℝ) - (bc.s : ℝ) * t := by
  have hs : (0 : ℝ) ≤ (bc.s : ℝ) := by exact_mod_cast hv.2.2.2.1
  have hden : (0 : ℝ) < (bc.m0 : ℝ) - (bc.s : ℝ) * (bc.h : ℝ) := by
    have := sDenom_pos bc hv; rw [sDenom] at this; push_cast at this; linarith
  have hmono : (bc.s : ℝ) * t ≤ (bc.s : ℝ) * (bc.h : ℝ) :=
    mul_le_mul_of_nonneg_left ht.2 hs
  linarith

theorem wReal_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) bc.h) : 0 < bc.wReal t := by
  rw [wReal]; exact div_pos one_pos (wDenom_pos bc hv ht)

theorem wReal_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) bc.h) : bc.wReal t ≤ 1 / (bc.sDenom : ℝ) := by
  have hs : (0 : ℝ) ≤ (bc.s : ℝ) := by exact_mod_cast hv.2.2.2.1
  have hden : (0 : ℝ) < (bc.m0 : ℝ) - (bc.s : ℝ) * t := wDenom_pos bc hv ht
  have hsd : (0 : ℝ) < (bc.sDenom : ℝ) := sDenom_pos bc hv
  have hle : (bc.sDenom : ℝ) ≤ (bc.m0 : ℝ) - (bc.s : ℝ) * t := by
    rw [sDenom]; push_cast
    have : (bc.s : ℝ) * t ≤ (bc.s : ℝ) * (bc.h : ℝ) := mul_le_mul_of_nonneg_left ht.2 hs
    linarith
  rw [wReal]
  exact div_le_div_of_nonneg_left one_pos.le hsd hle

omit hv in
theorem chiWPoly_eval {t : ℝ} :
    ev bc.chiWPoly t = ev bc.wPoly t * ((bc.m0 : ℝ) - (bc.s : ℝ) * t) - 1 := by
  rw [chiWPoly, ev_subtract, ev_multiply]
  congr 1
  · congr 1
    rw [ev_cons, ev_cons, ev_nil]; push_cast; ring
  · rw [ev_cons, ev_nil]; norm_num

/-- Result 1: the reciprocal mass is approximated by `ŵ` with error at most
`chiW / (m₀ - s h)` on the step. -/
theorem mass_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) bc.h) :
    |bc.wReal t - ev bc.wPoly t| ≤ (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by
  have hden : (0 : ℝ) < (bc.m0 : ℝ) - (bc.s : ℝ) * t := wDenom_pos bc hv ht
  have hw : bc.wReal t * ((bc.m0 : ℝ) - (bc.s : ℝ) * t) = 1 := by
    rw [wReal]; field_simp
  have hid : bc.wReal t - ev bc.wPoly t
      = bc.wReal t * (1 - ev bc.wPoly t * ((bc.m0 : ℝ) - (bc.s : ℝ) * t)) := by
    have : bc.wReal t * (ev bc.wPoly t * ((bc.m0 : ℝ) - (bc.s : ℝ) * t))
        = ev bc.wPoly t := by
      rw [show bc.wReal t * (ev bc.wPoly t * ((bc.m0 : ℝ) - (bc.s : ℝ) * t))
          = ev bc.wPoly t * (bc.wReal t * ((bc.m0 : ℝ) - (bc.s : ℝ) * t)) by ring, hw, mul_one]
    rw [mul_sub, mul_one, this]
  rw [hid, abs_mul]
  have hchi : |1 - ev bc.wPoly t * ((bc.m0 : ℝ) - (bc.s : ℝ) * t)| ≤ (bc.chiW : ℝ) := by
    rw [show 1 - ev bc.wPoly t * ((bc.m0 : ℝ) - (bc.s : ℝ) * t)
        = -(ev bc.chiWPoly t) by rw [chiWPoly_eval bc]; ring, abs_neg]
    exact ev_abs_le _ (Candidate.step_abs ht)
  have hwabs : |bc.wReal t| ≤ 1 / (bc.sDenom : ℝ) := by
    rw [abs_of_pos (wReal_pos bc hv ht)]; exact wReal_le bc hv ht
  have hsd : (0 : ℝ) < (bc.sDenom : ℝ) := sDenom_pos bc hv
  calc |bc.wReal t| * |1 - ev bc.wPoly t * ((bc.m0 : ℝ) - (bc.s : ℝ) * t)|
      ≤ (1 / (bc.sDenom : ℝ)) * (bc.chiW : ℝ) :=
        mul_le_mul hwabs hchi (abs_nonneg _) (by positivity)
    _ = (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by ring

/-- Result 1 corollary: `sup w ≤ wMax`. -/
theorem wMax_sound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) bc.h) : bc.wReal t ≤ (bc.wMax : ℝ) := by
  have h1 := mass_bound bc hv ht
  have h2 : |ev bc.wPoly t| ≤ (bound bc.wPoly bc.h : ℝ) := ev_abs_le _ (Candidate.step_abs ht)
  simp only [wMax]; push_cast
  have := (abs_le.mp h1).2
  have := (abs_le.mp h2).2
  linarith

omit hv in
/-- The sensitivity position candidate is bounded by `Gp`. -/
theorem Gp_sound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) bc.h) : ‖bc.gp t‖ ≤ (bc.Gp : ℝ) := by
  rw [gp]
  refine (pack_norm_le _ _).trans ?_
  have hx := ev_abs_le bc.gx (Candidate.step_abs ht)
  have hy := ev_abs_le bc.gy (Candidate.step_abs ht)
  simp only [Gp]; push_cast; linarith

omit hv in
/-- The sensitivity velocity candidate is bounded by `Gv`. -/
theorem Gv_sound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) bc.h) : ‖bc.gv t‖ ≤ (bc.Gv : ℝ) := by
  rw [gv]
  refine (pack_norm_le _ _).trans ?_
  have hx := ev_abs_le bc.gvx (Candidate.step_abs ht)
  have hy := ev_abs_le bc.gvy (Candidate.step_abs ht)
  simp only [Gv]; push_cast; linarith

end Sound
/-! ### Unit direction consequences -/

/-- The rational unit condition, transported to the reals. -/
theorem unit_dir_real (bc : BurnCandidate) (hv : bc.Valid) :
    (bc.ex : ℝ) ^ 2 + (bc.ey : ℝ) ^ 2 = 1 := by exact_mod_cast hv.2.2.2.2.2.2.1

theorem edir_norm (bc : BurnCandidate) (hv : bc.Valid) : ‖bc.edir‖ = 1 := by
  rw [edir, pack_norm, unit_dir_real bc hv, Real.sqrt_one]

theorem Jdir_norm (bc : BurnCandidate) (hv : bc.Valid) : ‖bc.Jdir‖ = 1 := by
  rw [Jdir, pack_norm]
  have h : (-(bc.ey : ℝ)) ^ 2 + (bc.ex : ℝ) ^ 2 = 1 := by
    have := unit_dir_real bc hv; nlinarith
  rw [h, Real.sqrt_one]

/-! ### Result 4: the misalignment chord remainder -/

/-- The second-order misalignment remainder: `‖R(δ)e - e - δ J e‖ ≤ δ²/2 + |δ|³/6`. -/
theorem misalign_bound (bc : BurnCandidate) (hv : bc.Valid) (δ : ℝ) :
    ‖bc.rotDir δ - bc.edir - δ • bc.Jdir‖ ≤ δ ^ 2 / 2 + |δ| ^ 3 / 6 := by
  have hunit := unit_dir_real bc hv
  have hvec : bc.rotDir δ - bc.edir - δ • bc.Jdir
      = pack ((bc.ex : ℝ) * (Real.cos δ - 1) - (bc.ey : ℝ) * (Real.sin δ - δ))
          ((bc.ex : ℝ) * (Real.sin δ - δ) + (bc.ey : ℝ) * (Real.cos δ - 1)) := by
    simp only [rotDir, edir, Jdir, pack_smul, pack_sub]
    congr 1 <;> ring
  rw [hvec, pack_norm]
  set A := Real.cos δ - 1 with hA
  set B := Real.sin δ - δ with hB
  have hns : ((bc.ex : ℝ) * A - (bc.ey : ℝ) * B) ^ 2 + ((bc.ex : ℝ) * B + (bc.ey : ℝ) * A) ^ 2
      = A ^ 2 + B ^ 2 := by
    have := hunit; nlinarith [this]
  rw [hns]
  have hsqle : A ^ 2 + B ^ 2 ≤ (|A| + |B|) ^ 2 := by
    nlinarith [sq_abs A, sq_abs B, abs_nonneg A, abs_nonneg B,
      mul_nonneg (abs_nonneg A) (abs_nonneg B)]
  have hmid : Real.sqrt (A ^ 2 + B ^ 2) ≤ |A| + |B| := by
    calc Real.sqrt (A ^ 2 + B ^ 2) ≤ Real.sqrt ((|A| + |B|) ^ 2) := Real.sqrt_le_sqrt hsqle
      _ = |A| + |B| := Real.sqrt_sq (by positivity)
  refine hmid.trans ?_
  have hcos : |A| ≤ δ ^ 2 / 2 := by
    rw [hA, abs_of_nonpos (by linarith [Real.cos_le_one δ])]
    linarith [one_sub_cos_le δ]
  have hsin : |B| ≤ |δ| ^ 3 / 6 := by
    rw [hB, abs_sub_comm]; exact abs_sub_sin_le δ
  linarith

/-! ### Result 2: the nominal thrust defect -/

/-- Result 2: the candidate acceleration matches gravity plus the nominal
thrust `f w(t) e` up to `Fx` on the step. -/
theorem nominal_defect (bc : BurnCandidate) (hv : bc.Valid)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) bc.h) :
    ‖bc.toCandidate.acc t - Gravity.field 1 (bc.toCandidate.pos t)
        - ((bc.f : ℝ) * bc.wReal t) • bc.edir‖ ≤ (bc.Fx : ℝ) := by
  set w := bc.wReal t with hw
  set ŵ := ev bc.wPoly t with hŵ
  set q := bc.toCandidate.pos t with hq
  set u := bc.toCandidate.invRadius t with hu
  -- term1 : the nominal thrust residual, a rational polynomial
  have hterm1 : bc.toCandidate.acc t + u ^ 3 • q - ((bc.f : ℝ) * ŵ) • bc.edir
      = pack (ev bc.resNomXc t) (ev bc.resNomYc t) := by
    rw [hq, hu, Candidate.residual_identity, edir, pack_smul, pack_sub]
    congr 1
    · rw [resNomXc, ev_subtract, ev_scale]; push_cast; ring
    · rw [resNomYc, ev_subtract, ev_scale]; push_cast; ring
  have hb1 : ‖bc.toCandidate.acc t + u ^ 3 • q - ((bc.f : ℝ) * ŵ) • bc.edir‖ ≤ (bc.resNom : ℝ) := by
    rw [hterm1]
    refine (pack_norm_le _ _).trans ?_
    have hx := ev_abs_le bc.resNomXc (Candidate.step_abs ht)
    have hy := ev_abs_le bc.resNomYc (Candidate.step_abs ht)
    rw [resNom]; push_cast; linarith
  -- term2 : the inverse-cube field defect of the candidate
  have hb2 : ‖Gravity.field 1 q + u ^ 3 • q‖ ≤ (bc.toCandidate.fieldError : ℝ) := by
    rw [hq, hu]; exact Candidate.field_error_bound bc.toCandidate hv.1 ht
  -- term3 : the reciprocal-mass mismatch
  have hf0 : (0 : ℝ) ≤ (bc.f : ℝ) := by exact_mod_cast hv.2.2.1
  have hb3 : ‖((bc.f : ℝ) * (ŵ - w)) • bc.edir‖ ≤ (bc.f : ℝ) * (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, edir_norm bc hv, mul_one, abs_mul, abs_of_nonneg hf0]
    have hm : |ŵ - w| ≤ (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by
      rw [abs_sub_comm]; exact mass_bound bc hv ht
    calc (bc.f : ℝ) * |ŵ - w| ≤ (bc.f : ℝ) * ((bc.chiW : ℝ) / (bc.sDenom : ℝ)) :=
          mul_le_mul_of_nonneg_left hm hf0
      _ = (bc.f : ℝ) * (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by ring
  -- assemble
  have hsplit : bc.toCandidate.acc t - Gravity.field 1 q - ((bc.f : ℝ) * w) • bc.edir
      = (bc.toCandidate.acc t + u ^ 3 • q - ((bc.f : ℝ) * ŵ) • bc.edir)
        - (Gravity.field 1 q + u ^ 3 • q) + ((bc.f : ℝ) * (ŵ - w)) • bc.edir := by
    rw [show (bc.f : ℝ) * (ŵ - w) = (bc.f : ℝ) * ŵ - (bc.f : ℝ) * w by ring, sub_smul]
    abel
  rw [hq] at hsplit ⊢
  rw [hsplit, Fx]; push_cast
  calc ‖(bc.toCandidate.acc t + u ^ 3 • q - ((bc.f : ℝ) * ŵ) • bc.edir)
          - (Gravity.field 1 q + u ^ 3 • q) + ((bc.f : ℝ) * (ŵ - w)) • bc.edir‖
      ≤ ‖(bc.toCandidate.acc t + u ^ 3 • q - ((bc.f : ℝ) * ŵ) • bc.edir)
          - (Gravity.field 1 q + u ^ 3 • q)‖ + ‖((bc.f : ℝ) * (ŵ - w)) • bc.edir‖ :=
        norm_add_le _ _
    _ ≤ (‖bc.toCandidate.acc t + u ^ 3 • q - ((bc.f : ℝ) * ŵ) • bc.edir‖
          + ‖Gravity.field 1 q + u ^ 3 • q‖) + ‖((bc.f : ℝ) * (ŵ - w)) • bc.edir‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ ((bc.resNom : ℝ) + (bc.toCandidate.fieldError : ℝ))
          + (bc.f : ℝ) * (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by gcongr
    _ = (bc.resNom : ℝ) + (bc.toCandidate.fieldError : ℝ)
          + (bc.f : ℝ) * (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by ring
/-! ### Result 3: the sensitivity defect -/

/-- The polynomial lower block `B̂` acts on the sensitivity as the polynomial
combination `(BxPoly, ByPoly)`. -/
theorem alower_gp (bc : BurnCandidate) (t : ℝ) :
    act (Alower bc.toCandidate t) (bc.gp t) = pack (ev bc.BxPoly t) (ev bc.ByPoly t) := by
  have hu5 : ev bc.u5 t = (ev bc.u t) ^ 5 := by
    simp only [u5, Candidate.u3, ev_multiply]; ring
  have hu3 : ev bc.toCandidate.u3 t = (ev bc.u t) ^ 3 := by
    simp only [Candidate.u3, ev_multiply]; ring
  have hX : (bc.toCandidate.pos t) 0 = ev bc.x t := rfl
  have hY : (bc.toCandidate.pos t) 1 = ev bc.y t := rfl
  have hU : bc.toCandidate.invRadius t = ev bc.u t := rfl
  have hg0 : (bc.gp t) 0 = ev bc.gx t := rfl
  have hg1 : (bc.gp t) 1 = ev bc.gy t := rfl
  have a00 : (Alower bc.toCandidate t) 0 0
      = 3 * (ev bc.u t) ^ 5 * (ev bc.x t) * (ev bc.x t) - (ev bc.u t) ^ 3 := by
    simp only [Alower, hX, hU]; norm_num
  have a01 : (Alower bc.toCandidate t) 0 1
      = 3 * (ev bc.u t) ^ 5 * (ev bc.x t) * (ev bc.y t) := by
    simp only [Alower, hX, hY, hU]; norm_num
  have a10 : (Alower bc.toCandidate t) 1 0
      = 3 * (ev bc.u t) ^ 5 * (ev bc.y t) * (ev bc.x t) := by
    simp only [Alower, hX, hY, hU]; norm_num
  have a11 : (Alower bc.toCandidate t) 1 1
      = 3 * (ev bc.u t) ^ 5 * (ev bc.y t) * (ev bc.y t) - (ev bc.u t) ^ 3 := by
    simp only [Alower, hY, hU]; norm_num
  ext i
  rw [act_component, Fin.sum_univ_two]
  fin_cases i
  · show (Alower bc.toCandidate t) 0 0 * (bc.gp t) 0 + (Alower bc.toCandidate t) 0 1 * (bc.gp t) 1
        = pack (ev bc.BxPoly t) (ev bc.ByPoly t) 0
    rw [a00, a01, hg0, hg1, pack_apply_zero]
    simp only [BxPoly, bxx, bxy, ev_add, ev_multiply, ev_subtract, ev_scale, hu5, hu3]
    push_cast; ring
  · show (Alower bc.toCandidate t) 1 0 * (bc.gp t) 0 + (Alower bc.toCandidate t) 1 1 * (bc.gp t) 1
        = pack (ev bc.BxPoly t) (ev bc.ByPoly t) 1
    rw [a10, a11, hg0, hg1, pack_apply_one]
    simp only [ByPoly, byx, byy, ev_add, ev_multiply, ev_subtract, ev_scale, hu5, hu3]
    push_cast; ring

/-- Result 3: the candidate sensitivity velocity derivative matches the true
gradient acting on the sensitivity position plus `f w(t) J e` up to `Fg`. -/
theorem sensitivity_defect (bc : BurnCandidate) (hv : bc.Valid) (hρ : 0 < bc.rhoMin)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) bc.h) :
    ‖bc.dgv t - act (Dg (bc.toCandidate.pos t)) (bc.gp t)
        - ((bc.f : ℝ) * bc.wReal t) • bc.Jdir‖ ≤ (bc.Fg : ℝ) := by
  set w := bc.wReal t with hw
  set ŵ := ev bc.wPoly t with hŵ
  set q := bc.toCandidate.pos t with hq
  -- term1 : the sensitivity residual, a rational polynomial
  have hterm1 : bc.dgv t - act (Alower bc.toCandidate t) (bc.gp t) - ((bc.f : ℝ) * ŵ) • bc.Jdir
      = pack (ev bc.resSensXc t) (ev bc.resSensYc t) := by
    rw [dgv, alower_gp, Jdir, pack_smul, pack_sub, pack_sub]
    congr 1
    · rw [resSensXc, ev_subtract, ev_subtract, ev_scale]; push_cast; ring
    · rw [resSensYc, ev_subtract, ev_subtract, ev_scale]; push_cast; ring
  have hb1 : ‖bc.dgv t - act (Alower bc.toCandidate t) (bc.gp t) - ((bc.f : ℝ) * ŵ) • bc.Jdir‖
      ≤ (bc.resG : ℝ) := by
    rw [hterm1]
    refine (pack_norm_le _ _).trans ?_
    have hx := ev_abs_le bc.resSensXc (Candidate.step_abs ht)
    have hy := ev_abs_le bc.resSensYc (Candidate.step_abs ht)
    rw [resG]; push_cast; linarith
  -- term2 : the gradient candidate error
  have hb2 : ‖act (Alower bc.toCandidate t) (bc.gp t) - act (Dg q) (bc.gp t)‖
      ≤ (GNC.PlanarCoast.epsA bc.toCandidate : ℝ) * (bc.Gp : ℝ) := by
    rw [hq, ← act_sub]
    refine (mulVec_norm_le_frobenius _ _).trans ?_
    have hfrob : frob (Alower bc.toCandidate t - Dg (bc.toCandidate.pos t))
        ≤ (GNC.PlanarCoast.epsA bc.toCandidate : ℝ) := by
      rw [frob_sub_comm]; exact gradient_candidate_error bc.toCandidate hv.1 hρ ht
    exact mul_le_mul hfrob (Gp_sound bc ht) (norm_nonneg _)
      (le_trans (frob_nonneg _) hfrob)
  -- term3 : the reciprocal-mass mismatch
  have hf0 : (0 : ℝ) ≤ (bc.f : ℝ) := by exact_mod_cast hv.2.2.1
  have hb3 : ‖((bc.f : ℝ) * (ŵ - w)) • bc.Jdir‖ ≤ (bc.f : ℝ) * (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, Jdir_norm bc hv, mul_one, abs_mul, abs_of_nonneg hf0]
    have hm : |ŵ - w| ≤ (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by
      rw [abs_sub_comm]; exact mass_bound bc hv ht
    calc (bc.f : ℝ) * |ŵ - w| ≤ (bc.f : ℝ) * ((bc.chiW : ℝ) / (bc.sDenom : ℝ)) :=
          mul_le_mul_of_nonneg_left hm hf0
      _ = (bc.f : ℝ) * (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by ring
  -- assemble
  have hsplit : bc.dgv t - act (Dg q) (bc.gp t) - ((bc.f : ℝ) * w) • bc.Jdir
      = (bc.dgv t - act (Alower bc.toCandidate t) (bc.gp t) - ((bc.f : ℝ) * ŵ) • bc.Jdir)
        + (act (Alower bc.toCandidate t) (bc.gp t) - act (Dg q) (bc.gp t))
        + ((bc.f : ℝ) * (ŵ - w)) • bc.Jdir := by
    rw [show (bc.f : ℝ) * (ŵ - w) = (bc.f : ℝ) * ŵ - (bc.f : ℝ) * w by ring, sub_smul]
    abel
  rw [hsplit, Fg]; push_cast
  calc ‖(bc.dgv t - act (Alower bc.toCandidate t) (bc.gp t) - ((bc.f : ℝ) * ŵ) • bc.Jdir)
          + (act (Alower bc.toCandidate t) (bc.gp t) - act (Dg q) (bc.gp t))
          + ((bc.f : ℝ) * (ŵ - w)) • bc.Jdir‖
      ≤ ‖(bc.dgv t - act (Alower bc.toCandidate t) (bc.gp t) - ((bc.f : ℝ) * ŵ) • bc.Jdir)
          + (act (Alower bc.toCandidate t) (bc.gp t) - act (Dg q) (bc.gp t))‖
          + ‖((bc.f : ℝ) * (ŵ - w)) • bc.Jdir‖ := norm_add_le _ _
    _ ≤ ((bc.resG : ℝ) + (GNC.PlanarCoast.epsA bc.toCandidate : ℝ) * (bc.Gp : ℝ))
          + (bc.f : ℝ) * (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hb1 hb2)
    _ = (bc.resG : ℝ) + (GNC.PlanarCoast.epsA bc.toCandidate : ℝ) * (bc.Gp : ℝ)
          + (bc.f : ℝ) * (bc.chiW : ℝ) / (bc.sDenom : ℝ) := by ring
/-! ### Result 5: the linearized error dynamics of the burn -/

/-- The deviation of a true trajectory `(Q, V)` from the segment `x̂ + δ ĝ`. -/
def dev (bc : BurnCandidate) (Q V : ℝ → E2) (δ : ℝ) (s : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  join2 (Q s - bc.toCandidate.pos s - δ • bc.gp s) (V s - bc.toCandidate.dpos s - δ • bc.gv s)

/-- The forcing term of the linearized error dynamics, supported on the
velocity block. -/
def noise (bc : BurnCandidate) (Q _V : ℝ → E2) (δ : ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  join2 (0 : E2)
    ((Gravity.field 1 (Q t) + bc.thrustAcc δ t - bc.toCandidate.acc t - δ • bc.dgv t)
      - act (Dg (bc.toCandidate.pos t)) (Q t - bc.toCandidate.pos t - δ • bc.gp t))

/-- Result 5: for a true burn trajectory `q'' = g(q) + f w(t) R(δ) e` with
`|δ| ≤ α`, the deviation from the segment `x̂ + δ ĝ` obeys the transported
linear error dynamics `e' = A(t) e + n(t)` with `n(t)` supported on the
velocity block and, inside the tube `‖e t‖ ≤ M` with `M + α Gp < ρmin`, bounded
by `K_R ‖e t‖² + Ftot`. -/
theorem error_dynamics_burn (bc : BurnCandidate) (hv : bc.Valid)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) bc.h) {M δ : ℝ}
    (hδ : |δ| ≤ (bc.alpha : ℝ))
    (hcond : M + (bc.alpha : ℝ) * (bc.Gp : ℝ) < (bc.rhoMin : ℝ))
    {Q V : ℝ → E2}
    (hQ : HasDerivAt Q (V t) t)
    (hVeq : HasDerivAt V (Gravity.field 1 (Q t) + bc.thrustAcc δ t) t)
    (heM : ‖dev bc Q V δ t‖ ≤ M) :
    HasDerivAt (dev bc Q V δ)
        (act (Amat (bc.toCandidate.pos t)) (dev bc Q V δ t) + noise bc Q V δ t) t
      ∧ (noise bc Q V δ t) 0 = 0 ∧ (noise bc Q V δ t) 1 = 0
      ∧ ‖noise bc Q V δ t‖
          ≤ (3 / ((bc.rhoMin : ℝ) - M - (bc.alpha : ℝ) * (bc.Gp : ℝ)) ^ 4)
              * ‖dev bc Q V δ t‖ ^ 2
            + ((bc.Fx : ℝ) + (bc.alpha : ℝ) * (bc.Fg : ℝ) + (bc.Fmis : ℝ)
              + (3 / ((bc.rhoMin : ℝ) - M - (bc.alpha : ℝ) * (bc.Gp : ℝ)) ^ 4)
                  * (bc.alpha : ℝ) ^ 2 * (bc.Gp : ℝ) ^ 2
              + 2 * (3 / ((bc.rhoMin : ℝ) - M - (bc.alpha : ℝ) * (bc.Gp : ℝ)) ^ 4)
                  * (bc.alpha : ℝ) * (bc.Gp : ℝ) * M) := by
  -- Part A: the linear error dynamics
  have hA : HasDerivAt (dev bc Q V δ)
      (act (Amat (bc.toCandidate.pos t)) (dev bc Q V δ t) + noise bc Q V δ t) t := by
    have e1 : bc.gvx = differentiate bc.gx := hv.2.2.2.2.2.2.2.1
    have e2 : bc.gvy = differentiate bc.gy := hv.2.2.2.2.2.2.2.2
    have hgvdgp : bc.gv t = bc.dgp t := by rw [gv, dgp, e1, e2]
    have hpos : HasDerivAt (fun s => Q s - bc.toCandidate.pos s - δ • bc.gp s)
        (V t - bc.toCandidate.dpos t - δ • bc.gv t) t := by
      have hp := (hQ.sub (bc.toCandidate.pos_hasDerivAt t)).sub
        ((bc.gp_hasDerivAt t).const_smul δ)
      rwa [hgvdgp]
    have hvel : HasDerivAt (fun s => V s - bc.toCandidate.dpos s - δ • bc.gv s)
        (Gravity.field 1 (Q t) + bc.thrustAcc δ t - bc.toCandidate.acc t - δ • bc.dgv t) t :=
      (hVeq.sub (bc.toCandidate.dpos_hasDerivAt t)).sub ((bc.gv_hasDerivAt t).const_smul δ)
    have hd := join2_hasDerivAt hpos hvel
    have heq : act (Amat (bc.toCandidate.pos t)) (dev bc Q V δ t) + noise bc Q V δ t
        = join2 (V t - bc.toCandidate.dpos t - δ • bc.gv t)
            (Gravity.field 1 (Q t) + bc.thrustAcc δ t - bc.toCandidate.acc t - δ • bc.dgv t) := by
      rw [dev, noise, act_Amat, join2_add]
      congr 1 <;> abel
    rw [heq]; exact hd
  refine ⟨hA, rfl, rfl, ?_⟩
  -- Part D: the forcing bound
  have hf0 : (0 : ℝ) ≤ (bc.f : ℝ) := by exact_mod_cast hv.2.2.1
  have halpha0 : (0 : ℝ) ≤ (bc.alpha : ℝ) := by exact_mod_cast hv.2.2.2.2.2.1
  have hGp0 : (0 : ℝ) ≤ (bc.Gp : ℝ) := le_trans (norm_nonneg _) (Gp_sound bc ht)
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) heM
  have hw0 : 0 < bc.wReal t := wReal_pos bc hv ht
  set ρ := ‖dev bc Q V δ t‖ with hρ
  set kR := (3 : ℝ) / ((bc.rhoMin : ℝ) - M - (bc.alpha : ℝ) * (bc.Gp : ℝ)) ^ 4 with hkR
  have hdenpos : (0 : ℝ) < (bc.rhoMin : ℝ) - M - (bc.alpha : ℝ) * (bc.Gp : ℝ) := by linarith
  have hkR0 : (0 : ℝ) ≤ kR := by rw [hkR]; positivity
  rw [noise, join2_left_zero_norm]
  set disp := Q t - bc.toCandidate.pos t with hdisp
  -- the displacement tube radius
  have hdisp_rho : ‖disp‖ ≤ ρ + (bc.alpha : ℝ) * (bc.Gp : ℝ) := by
    have hsplit : disp = (Q t - bc.toCandidate.pos t - δ • bc.gp t) + δ • bc.gp t := by
      rw [hdisp]; abel
    have hgpsmul : ‖δ • bc.gp t‖ ≤ (bc.alpha : ℝ) * (bc.Gp : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hδ (Gp_sound bc ht) (norm_nonneg _) halpha0
    have hep : ‖Q t - bc.toCandidate.pos t - δ • bc.gp t‖ ≤ ρ := by
      rw [hρ]; exact norm_le_join2_left _ _
    calc ‖disp‖ = ‖(Q t - bc.toCandidate.pos t - δ • bc.gp t) + δ • bc.gp t‖ := by rw [hsplit]
      _ ≤ ‖Q t - bc.toCandidate.pos t - δ • bc.gp t‖ + ‖δ • bc.gp t‖ := norm_add_le _ _
      _ ≤ ρ + (bc.alpha : ℝ) * (bc.Gp : ℝ) := add_le_add hep hgpsmul
  have hdispbound : ‖disp‖ ≤ M + (bc.alpha : ℝ) * (bc.Gp : ℝ) := by
    have : ρ ≤ M := heM
    linarith
  -- the second-order field remainder on the displacement tube
  have hrvec : ‖Gravity.field 1 (Q t) - Gravity.field 1 (bc.toCandidate.pos t)
        - act (Dg (bc.toCandidate.pos t)) disp‖ ≤ kR * ‖disp‖ ^ 2 := by
    have hq : (bc.rhoMin : ℝ) ≤ ‖bc.toCandidate.pos t‖ :=
      bc.toCandidate.rhoMin_le_norm_pos hv.1 ht
    have hMlt : M + (bc.alpha : ℝ) * (bc.Gp : ℝ) < (bc.rhoMin : ℝ) := hcond
    have hrem := field_taylor_remainder (bc.toCandidate.pos t) disp hMlt hq hdispbound
    have hQeq : bc.toCandidate.pos t + disp = Q t := by rw [hdisp]; abel
    rw [hQeq] at hrem
    have hc : (3 : ℝ) / ((bc.rhoMin : ℝ) - (M + (bc.alpha : ℝ) * (bc.Gp : ℝ))) ^ 4 = kR := by
      rw [hkR]; ring_nf
    rwa [hc] at hrem
  -- the defect bounds
  have hδx : ‖bc.toCandidate.acc t - Gravity.field 1 (bc.toCandidate.pos t)
        - ((bc.f : ℝ) * bc.wReal t) • bc.edir‖ ≤ (bc.Fx : ℝ) := nominal_defect bc hv ht
  have hδg : ‖bc.dgv t - act (Dg (bc.toCandidate.pos t)) (bc.gp t)
        - ((bc.f : ℝ) * bc.wReal t) • bc.Jdir‖ ≤ (bc.Fg : ℝ) :=
    sensitivity_defect bc hv hv.2.1 ht
  have hδδg : ‖δ • (bc.dgv t - act (Dg (bc.toCandidate.pos t)) (bc.gp t)
        - ((bc.f : ℝ) * bc.wReal t) • bc.Jdir)‖ ≤ (bc.alpha : ℝ) * (bc.Fg : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hδ hδg (norm_nonneg _) halpha0
  have hmis : ‖((bc.f : ℝ) * bc.wReal t) • (bc.rotDir δ - bc.edir - δ • bc.Jdir)‖
      ≤ (bc.Fmis : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf0 hw0.le)]
    have hchordv := misalign_bound bc hv δ
    have hd2 : δ ^ 2 ≤ (bc.alpha : ℝ) ^ 2 := by
      have h := sq_abs δ; nlinarith [hδ, abs_nonneg δ, halpha0]
    have hd3 : |δ| ^ 3 ≤ (bc.alpha : ℝ) ^ 3 := by
      have h := pow_le_pow_left₀ (abs_nonneg δ) hδ 3; simpa using h
    have hchord : δ ^ 2 / 2 + |δ| ^ 3 / 6 ≤ (bc.alpha : ℝ) ^ 2 / 2 + (bc.alpha : ℝ) ^ 3 / 6 := by
      linarith
    have hchord0 : (0 : ℝ) ≤ (bc.alpha : ℝ) ^ 2 / 2 + (bc.alpha : ℝ) ^ 3 / 6 := by positivity
    have hwmax : bc.wReal t ≤ (bc.wMax : ℝ) := wMax_sound bc hv ht
    calc (bc.f : ℝ) * bc.wReal t * ‖bc.rotDir δ - bc.edir - δ • bc.Jdir‖
        ≤ (bc.f : ℝ) * bc.wReal t * (δ ^ 2 / 2 + |δ| ^ 3 / 6) :=
          mul_le_mul_of_nonneg_left hchordv (mul_nonneg hf0 hw0.le)
      _ ≤ (bc.f : ℝ) * bc.wReal t * ((bc.alpha : ℝ) ^ 2 / 2 + (bc.alpha : ℝ) ^ 3 / 6) :=
          mul_le_mul_of_nonneg_left hchord (mul_nonneg hf0 hw0.le)
      _ ≤ (bc.f : ℝ) * (bc.wMax : ℝ) * ((bc.alpha : ℝ) ^ 2 / 2 + (bc.alpha : ℝ) ^ 3 / 6) := by
          apply mul_le_mul_of_nonneg_right _ hchord0
          exact mul_le_mul_of_nonneg_left hwmax hf0
      _ = (bc.Fmis : ℝ) := by rw [Fmis]; push_cast; ring
  -- the noise decomposition
  have hnv : (Gravity.field 1 (Q t) + bc.thrustAcc δ t - bc.toCandidate.acc t - δ • bc.dgv t)
        - act (Dg (bc.toCandidate.pos t)) (Q t - bc.toCandidate.pos t - δ • bc.gp t)
      = (Gravity.field 1 (Q t) - Gravity.field 1 (bc.toCandidate.pos t)
          - act (Dg (bc.toCandidate.pos t)) disp)
        - (bc.toCandidate.acc t - Gravity.field 1 (bc.toCandidate.pos t)
          - ((bc.f : ℝ) * bc.wReal t) • bc.edir)
        - δ • (bc.dgv t - act (Dg (bc.toCandidate.pos t)) (bc.gp t)
          - ((bc.f : ℝ) * bc.wReal t) • bc.Jdir)
        + ((bc.f : ℝ) * bc.wReal t) • (bc.rotDir δ - bc.edir - δ • bc.Jdir) := by
    have hact : act (Dg (bc.toCandidate.pos t)) (Q t - bc.toCandidate.pos t - δ • bc.gp t)
        = act (Dg (bc.toCandidate.pos t)) disp - δ • act (Dg (bc.toCandidate.pos t)) (bc.gp t) := by
      rw [show Q t - bc.toCandidate.pos t - δ • bc.gp t = disp - δ • bc.gp t by rw [hdisp],
        act_vsub, act_vsmul]
    rw [thrustAcc, hact]
    module
  rw [hnv]
  -- displacement squared bound
  have hdisp2 : ‖disp‖ ^ 2 ≤ ρ ^ 2 + (bc.alpha : ℝ) ^ 2 * (bc.Gp : ℝ) ^ 2
      + 2 * (bc.alpha : ℝ) * (bc.Gp : ℝ) * M := by
    have h1 : ‖disp‖ ^ 2 ≤ (ρ + (bc.alpha : ℝ) * (bc.Gp : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hdisp_rho 2
    have hρM : ρ ≤ M := heM
    nlinarith [h1, hρM, halpha0, hGp0, mul_nonneg halpha0 hGp0]
  have hkrdisp : kR * ‖disp‖ ^ 2
      ≤ kR * ρ ^ 2 + kR * (bc.alpha : ℝ) ^ 2 * (bc.Gp : ℝ) ^ 2
        + 2 * kR * (bc.alpha : ℝ) * (bc.Gp : ℝ) * M := by
    have h := mul_le_mul_of_nonneg_left hdisp2 hkR0
    refine h.trans (le_of_eq ?_); ring
  calc ‖(Gravity.field 1 (Q t) - Gravity.field 1 (bc.toCandidate.pos t)
            - act (Dg (bc.toCandidate.pos t)) disp)
          - (bc.toCandidate.acc t - Gravity.field 1 (bc.toCandidate.pos t)
            - ((bc.f : ℝ) * bc.wReal t) • bc.edir)
          - δ • (bc.dgv t - act (Dg (bc.toCandidate.pos t)) (bc.gp t)
            - ((bc.f : ℝ) * bc.wReal t) • bc.Jdir)
          + ((bc.f : ℝ) * bc.wReal t) • (bc.rotDir δ - bc.edir - δ • bc.Jdir)‖
      ≤ kR * ‖disp‖ ^ 2 + (bc.Fx : ℝ) + (bc.alpha : ℝ) * (bc.Fg : ℝ) + (bc.Fmis : ℝ) := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add
          ((norm_sub_le _ _).trans (add_le_add hrvec hδx)) hδδg)) hmis
    _ ≤ kR * ρ ^ 2
          + ((bc.Fx : ℝ) + (bc.alpha : ℝ) * (bc.Fg : ℝ) + (bc.Fmis : ℝ)
            + kR * (bc.alpha : ℝ) ^ 2 * (bc.Gp : ℝ) ^ 2
            + 2 * kR * (bc.alpha : ℝ) * (bc.Gp : ℝ) * M) := by
        linarith [hkrdisp]

/-! ### Coast reduction and nonnegativity of the forcing constants -/

/-- With zero thrust the burn equations are those of a coordinate solution of
`PolynomialOrbit.physicalRate 0`, for every misalignment angle. -/
theorem coast_reduction (bc : BurnCandidate) (hf : bc.f = 0) (δ : ℝ)
    {w : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hw : HasDerivAt w (PolynomialOrbit.physicalRate 0 (w t)) t) :
    HasDerivAt (Candidate.truePos w) (Candidate.trueVel w t) t
      ∧ HasDerivAt (Candidate.trueVel w)
          (Gravity.field 1 (Candidate.truePos w t) + bc.thrustAcc δ t) t := by
  refine ⟨Candidate.truePos_hasDerivAt hw, ?_⟩
  have h0 : bc.thrustAcc δ t = 0 := by simp [thrustAcc, hf]
  rw [h0, add_zero]
  exact Candidate.trueVel_hasDerivAt hw

section Nonneg
variable (bc : BurnCandidate) (hv : bc.Valid)
include hv

theorem chiW_nonneg : 0 ≤ bc.chiW := bound_nonneg _ hv.1.1

theorem wMax_nonneg : 0 ≤ bc.wMax :=
  add_nonneg (bound_nonneg _ hv.1.1) (div_nonneg (chiW_nonneg bc hv) hv.2.2.2.2.1.le)

theorem Gp_nonneg : 0 ≤ bc.Gp := add_nonneg (bound_nonneg _ hv.1.1) (bound_nonneg _ hv.1.1)

theorem fieldError_nonneg : 0 ≤ bc.toCandidate.fieldError := by
  have hchi : 0 ≤ bc.toCandidate.chi := bound_nonneg _ hv.1.1
  have hzmax : 0 ≤ bc.toCandidate.zMax :=
    mul_nonneg hv.1.2.2.2.2.1 (bound_nonneg _ hv.1.1)
  have hzmin : 0 ≤ bc.toCandidate.zMin := mul_nonneg hv.1.2.2.2.1 hv.1.2.2.1.le
  unfold Candidate.fieldError
  exact div_nonneg (mul_nonneg (div_nonneg hchi hv.1.2.1.le) (by positivity)) (by linarith)

theorem epsA_nonneg : 0 ≤ GNC.PlanarCoast.epsA bc.toCandidate := by
  have hchi : 0 ≤ bc.toCandidate.chi := bound_nonneg _ hv.1.1
  have hzmax : 0 ≤ bc.toCandidate.zMax :=
    mul_nonneg hv.1.2.2.2.2.1 (bound_nonneg _ hv.1.1)
  have hzmin : 0 ≤ bc.toCandidate.zMin := mul_nonneg hv.1.2.2.2.1 hv.1.2.2.1.le
  have hr : 0 ≤ bc.rhoMin := hv.2.1.le
  have hrho2 : 0 ≤ bc.toCandidate.rho2Max := bound_nonneg _ hv.1.1
  have hA3 : 0 ≤ GNC.PlanarCoast.A3 bc.toCandidate := by
    unfold GNC.PlanarCoast.A3
    exact div_nonneg (mul_nonneg hchi (by positivity)) (mul_nonneg (by linarith) (by positivity))
  have hA5 : 0 ≤ GNC.PlanarCoast.A5 bc.toCandidate := by
    unfold GNC.PlanarCoast.A5
    exact div_nonneg (mul_nonneg hchi (by positivity)) (mul_nonneg (by linarith) (by positivity))
  unfold GNC.PlanarCoast.epsA
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrho2) hA5)
    (mul_nonneg (by norm_num) hA3)

theorem Fx_nonneg : 0 ≤ bc.Fx := by
  unfold Fx resNom
  exact add_nonneg (add_nonneg (add_nonneg (bound_nonneg _ hv.1.1) (bound_nonneg _ hv.1.1))
    (fieldError_nonneg bc hv))
    (div_nonneg (mul_nonneg hv.2.2.1 (chiW_nonneg bc hv)) hv.2.2.2.2.1.le)

theorem Fg_nonneg : 0 ≤ bc.Fg := by
  unfold Fg resG
  exact add_nonneg (add_nonneg (add_nonneg (bound_nonneg _ hv.1.1) (bound_nonneg _ hv.1.1))
    (mul_nonneg (epsA_nonneg bc hv) (Gp_nonneg bc hv)))
    (div_nonneg (mul_nonneg hv.2.2.1 (chiW_nonneg bc hv)) hv.2.2.2.2.1.le)

theorem Fmis_nonneg : 0 ≤ bc.Fmis := by
  have ha : 0 ≤ bc.alpha := hv.2.2.2.2.2.1
  unfold Fmis
  exact mul_nonneg (mul_nonneg hv.2.2.1 (wMax_nonneg bc hv)) (by positivity)

/-- The constant forcing term `Ftot` of `error_dynamics_burn` is nonnegative,
as required by the transported step and chain bounds. -/
theorem Ftot_nonneg {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ (bc.Fx : ℝ) + (bc.alpha : ℝ) * (bc.Fg : ℝ) + (bc.Fmis : ℝ)
      + (3 / ((bc.rhoMin : ℝ) - M - (bc.alpha : ℝ) * (bc.Gp : ℝ)) ^ 4)
          * (bc.alpha : ℝ) ^ 2 * (bc.Gp : ℝ) ^ 2
      + 2 * (3 / ((bc.rhoMin : ℝ) - M - (bc.alpha : ℝ) * (bc.Gp : ℝ)) ^ 4)
          * (bc.alpha : ℝ) * (bc.Gp : ℝ) * M := by
  have hx : (0 : ℝ) ≤ bc.Fx := by exact_mod_cast Fx_nonneg bc hv
  have hg : (0 : ℝ) ≤ bc.Fg := by exact_mod_cast Fg_nonneg bc hv
  have hm : (0 : ℝ) ≤ bc.Fmis := by exact_mod_cast Fmis_nonneg bc hv
  have ha : (0 : ℝ) ≤ bc.alpha := by exact_mod_cast hv.2.2.2.2.2.1
  have hG : (0 : ℝ) ≤ bc.Gp := by exact_mod_cast Gp_nonneg bc hv
  have hK : (0 : ℝ) ≤ 3 / ((bc.rhoMin : ℝ) - M - (bc.alpha : ℝ) * (bc.Gp : ℝ)) ^ 4 := by
    positivity
  have h1 := mul_nonneg ha hg
  have h2 := mul_nonneg (mul_nonneg hK (pow_nonneg ha 2)) (pow_nonneg hG 2)
  have h3 := mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK) ha) hG) hM
  linarith

end Nonneg

end BurnCandidate

/-! ### Result 6: the handoff mismatch -/

/-- The deviation mismatch at a step boundary is the candidate jump plus `δ`
times the sensitivity jump, so its norm is at most `dX + α dG`. -/
theorem handoff_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (jc js : F) (δ dX dG α : ℝ) (hjc : ‖jc‖ ≤ dX) (hjs : ‖js‖ ≤ dG)
    (hδ : |δ| ≤ α) : ‖jc + δ • js‖ ≤ dX + α * dG := by
  have hα0 : 0 ≤ α := le_trans (abs_nonneg δ) hδ
  calc ‖jc + δ • js‖ ≤ ‖jc‖ + ‖δ • js‖ := norm_add_le _ _
    _ = ‖jc‖ + |δ| * ‖js‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ dX + α * dG := add_le_add hjc (mul_le_mul hδ hjs (norm_nonneg _) hα0)

/-! ### Result 7: reading the reachable set -/

/-- Segment form: a terminal deviation bound places the terminal position in the
Minkowski sum of the sensitivity segment and the ball of radius `E`. -/
theorem reachable_segment {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p ph g : F) (δ E α : ℝ) (hδ : |δ| ≤ α) (hE : ‖p - ph - δ • g‖ ≤ E) :
    ∃ δ', |δ'| ≤ α ∧ ‖p - ph - δ' • g‖ ≤ E := ⟨δ, hδ, hE⟩

/-- Support-function form: for every unit direction the terminal position support
is bounded by the nominal support, the sensitivity support scaled by `α`, and `E`. -/
theorem reachable_support (p ph g u : E2) (δ E α : ℝ) (hu : ‖u‖ = 1)
    (hδ : |δ| ≤ α) (hE : ‖p - ph - δ • g‖ ≤ E) :
    (inner ℝ u p : ℝ) ≤ (inner ℝ u ph : ℝ) + α * |(inner ℝ u g : ℝ)| + E := by
  have hinner : (inner ℝ u (p - ph - δ • g) : ℝ)
      = (inner ℝ u p : ℝ) - (inner ℝ u ph : ℝ) - δ * (inner ℝ u g : ℝ) := by
    rw [inner_sub_right, inner_sub_right, inner_smul_right]
  have h1 : (inner ℝ u p : ℝ) - (inner ℝ u ph : ℝ) - δ * (inner ℝ u g : ℝ) ≤ E := by
    rw [← hinner]
    calc (inner ℝ u (p - ph - δ • g) : ℝ) ≤ |(inner ℝ u (p - ph - δ • g) : ℝ)| := le_abs_self _
      _ ≤ ‖u‖ * ‖p - ph - δ • g‖ := abs_real_inner_le_norm u _
      _ = ‖p - ph - δ • g‖ := by rw [hu, one_mul]
      _ ≤ E := hE
  have h2 : δ * (inner ℝ u g : ℝ) ≤ α * |(inner ℝ u g : ℝ)| := by
    calc δ * (inner ℝ u g : ℝ) ≤ |δ * (inner ℝ u g : ℝ)| := le_abs_self _
      _ = |δ| * |(inner ℝ u g : ℝ)| := abs_mul _ _
      _ ≤ α * |(inner ℝ u g : ℝ)| := mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  linarith

/-! ### Result 8: planar orbital enclosure of the reachable set -/

/-- The planar specific angular momentum `q₁ v₂ - q₂ v₁`. -/
def planarMom (q v : E2) : ℝ := q 0 * v 1 - q 1 * v 0

/-- The two dimensional cross determinant is bounded by the product of norms. -/
theorem cross_abs_le (p d : E2) : |p 0 * d 1 - p 1 * d 0| ≤ ‖p‖ * ‖d‖ := by
  have hp : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq p, Fin.sum_univ_two]
  have hd : ‖d‖ ^ 2 = (d 0) ^ 2 + (d 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq d, Fin.sum_univ_two]
  have hsq : (p 0 * d 1 - p 1 * d 0) ^ 2 ≤ (‖p‖ * ‖d‖) ^ 2 := by
    rw [mul_pow, hp, hd]; nlinarith [sq_nonneg (p 0 * d 0 + p 1 * d 1)]
  have hb : 0 ≤ ‖p‖ * ‖d‖ := by positivity
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt ((p 0 * d 1 - p 1 * d 0) ^ 2) ≤ Real.sqrt ((‖p‖ * ‖d‖) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖p‖ * ‖d‖ := Real.sqrt_sq hb

/-- Planar angular-momentum enclosure: the momentum of a perturbed state differs
from the nominal by at most `‖p‖ V + P ‖v‖ + P V`. -/
theorem planar_momentum_bound (p v dp dv : E2) {P V : ℝ}
    (hp : ‖dp‖ ≤ P) (hvv : ‖dv‖ ≤ V) :
    |planarMom (p + dp) (v + dv) - planarMom p v| ≤ ‖p‖ * V + P * ‖v‖ + P * V := by
  have hP : 0 ≤ P := (norm_nonneg _).trans hp
  have hadd : ∀ (a b : E2) (i : Fin 2), (a + b) i = a i + b i := fun _ _ _ => rfl
  have he : planarMom (p + dp) (v + dv) - planarMom p v
      = (p 0 * dv 1 - p 1 * dv 0) + (dp 0 * v 1 - dp 1 * v 0)
        + (dp 0 * dv 1 - dp 1 * dv 0) := by
    simp only [planarMom, hadd]; ring
  have hb1 : |p 0 * dv 1 - p 1 * dv 0| ≤ ‖p‖ * V :=
    (cross_abs_le p dv).trans (mul_le_mul_of_nonneg_left hvv (norm_nonneg _))
  have hb2 : |dp 0 * v 1 - dp 1 * v 0| ≤ P * ‖v‖ :=
    (cross_abs_le dp v).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  have hb3 : |dp 0 * dv 1 - dp 1 * dv 0| ≤ P * V :=
    (cross_abs_le dp dv).trans (mul_le_mul hp hvv (norm_nonneg _) hP)
  rw [he]
  refine (abs_add_le _ _).trans ?_
  exact add_le_add ((abs_add_le _ _).trans (add_le_add hb1 hb2)) hb3

/-- Orbital enclosure of the reachable set: the specific energy and planar
angular momentum of every reachable state differ from the nominal by the
`OrbitEnclosure` bounds evaluated at the radii `P = α Gp + Ep` and
`V = α Gv + Ev`, with separate position and velocity deviation bounds. -/
theorem reachable_orbit_enclosure (ph vh gp gv q v : E2) {δ Ep Ev α Gp Gv : ℝ}
    (hδ : |δ| ≤ α) (hgp : ‖gp‖ ≤ Gp) (hgv : ‖gv‖ ≤ Gv)
    (hqp : ‖q - ph - δ • gp‖ ≤ Ep) (hqv : ‖v - vh - δ • gv‖ ≤ Ev)
    (hsmall : α * Gp + Ep < ‖ph‖) :
    |GNC.OrbitalEnergy.specificEnergy 1 q v - GNC.OrbitalEnergy.specificEnergy 1 ph vh|
        ≤ ‖vh‖ * (α * Gv + Ev) + (α * Gv + Ev) ^ 2 / 2
          + (α * Gp + Ep) / (‖ph‖ * (‖ph‖ - (α * Gp + Ep)))
      ∧ |planarMom q v - planarMom ph vh|
        ≤ ‖ph‖ * (α * Gv + Ev) + (α * Gp + Ep) * ‖vh‖ + (α * Gp + Ep) * (α * Gv + Ev) := by
  have hdp : ‖q - ph‖ ≤ α * Gp + Ep := by
    have h := handoff_bound (q - ph - δ • gp) gp δ Ep Gp α hqp hgp hδ
    rw [show q - ph - δ • gp + δ • gp = q - ph by abel] at h
    linarith
  have hdv : ‖v - vh‖ ≤ α * Gv + Ev := by
    have h := handoff_bound (v - vh - δ • gv) gv δ Ev Gv α hqv hgv hδ
    rw [show v - vh - δ • gv + δ • gv = v - vh by abel] at h
    linarith
  refine ⟨?_, ?_⟩
  · have henergy := GNC.OrbitEnclosure.energy_bound ph vh (q - ph) (v - vh)
      (mu := 1) (by norm_num) hdp hdv hsmall
    rwa [show ph + (q - ph) = q by abel, show vh + (v - vh) = v by abel, one_mul] at henergy
  · have hmom := planar_momentum_bound ph vh (q - ph) (v - vh) hdp hdv
    rwa [show ph + (q - ph) = q by abel, show vh + (v - vh) = v by abel] at hmom

/-! ### A decidable example -/

/-- A near-perigee coast-mass burn step (`m₀ = 1`, no mass depletion, thrust
along `e = (0, 1)`, zero first-order sensitivity). -/
def sampleBurn : BurnCandidate :=
  { x := [1, 0, -1/2], y := [0, 21/20], vx := [0, -1], vy := [21/20], u := [1],
    h := 1/10, rhoMin := 9/10, rhoMax := 11/10,
    wPoly := [1], gx := [], gy := [], gvx := [], gvy := [],
    f := 1/10, s := 0, m0 := 1, ex := 0, ey := 1, alpha := 1/10 }

example : sampleBurn.Valid := by decide +kernel

example : sampleBurn.chiW = 0 := by decide +kernel

end GNC.PlanarBurn
