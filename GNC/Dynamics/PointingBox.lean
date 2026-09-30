import GNC.Lie.ExponentialCoordinates
import GNC.Dynamics.PreintegrationGravityTransfer
import Mathlib.Analysis.Convex.Basic

/-! Independent logarithmic boxes for constant pointing uncertainty.
The physical group law, right/left errors, logarithmic reconstruction and
the mapped translation radius are checked here. Area formulae, plotting,
Python interval arithmetic and measured costs are not kernel claims.
-/
noncomputable section
set_option autoImplicit false
open Matrix Real
open scoped Matrix
namespace GNC.PointingBox

def nominal (r₀ c b : Vec3) : SE23 := ⟨1,c,r₀+b⟩
def actual (R : SO3) (ε : ℝ) (r₀ c b : Vec3) : SE23 :=
  ⟨R,(1+ε) • rotate R c,r₀+(1+ε) • rotate R b⟩

theorem right_error_general (R : SO3) (ε : ℝ) (r₀ c b : Vec3) :
    actual R ε r₀ c b * (nominal r₀ c b)⁻¹ =
      ⟨R,ε • rotate R c,r₀-rotate R r₀+ε • rotate R b⟩ := by
  apply SE23.ext
  · simp [actual, nominal]
  · simp [actual, nominal, rotate_neg]; module
  · simp [actual, nominal, rotate_neg, rotate_add]; module

/-- Attitude uncertainty about an unchanged thrust direction need not
produce any physical position uncertainty, even if the error log changes. -/
theorem unchanged_thrust_position (R : SO3) (r₀ c b : Vec3)
    (hb : rotate R b = b) : (actual R 0 r₀ c b).pos = r₀+b := by
  simp [actual, hb]

/-- Every convex physical enclosure contains the chord midpoint. This
obstruction applies to oriented boxes and ellipsoids as well as AABBs. -/
theorem convex_chord_midpoint {C : Set (ℝ × ℝ)} (hC : Convex ℝ C)
    (x y : ℝ) (hp : (x,y) ∈ C) (hm : (x,-y) ∈ C) : (x,0) ∈ C := by
  have h := hC hp hm (a := (1/2:ℝ)) (b := (1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> ext <;> simp <;> ring

theorem right_error (R : SO3) (ε : ℝ) (r₀ c b : Vec3)
    (hr : rotate R r₀ = r₀) :
    actual R ε r₀ c b * (nominal r₀ c b)⁻¹ =
      ⟨R,ε • rotate R c,ε • rotate R b⟩ := by
  apply SE23.ext
  · simp [actual, nominal]
  · simp [actual, nominal, rotate_neg]
    module
  · simp [actual, nominal, rotate_neg, rotate_add, hr]
    module

theorem left_error (R : SO3) (ε : ℝ) (r₀ c b : Vec3) :
    (nominal r₀ c b)⁻¹ * actual R ε r₀ c b =
      ⟨R,(1+ε) • rotate R c-c,(1+ε) • rotate R b-b⟩ := by
  apply SE23.ext
  · simp [actual, nominal]
  · simp [actual, nominal]; module
  · simp [actual, nominal]; module

def rightLog (φ c b : Vec3) (ε : ℝ) : LogState :=
  ![Jacobian.inverseAt φ (ε • rotate (rotationExp φ) b),
    Jacobian.inverseAt φ (ε • rotate (rotationExp φ) c),φ]

/-- Actual principal-chart logarithmic coordinates, not independent
coordinates substituted for a correlated physical uncertainty set. -/
theorem rightLog_exp (φ c b : Vec3) (ε : ℝ) (hφ : enorm φ < 2*π) :
    groupExp (rightLog φ c b ε) =
      ⟨rotationExp φ,ε • rotate (rotationExp φ) c,ε • rotate (rotationExp φ) b⟩ := by
  apply SE23.ext
  · rfl
  · exact Jacobian.leftAt_inverseAt_all _ _ hφ
  · exact Jacobian.leftAt_inverseAt_all _ _ hφ

theorem reconstruct (φ r₀ c b : Vec3) (ε : ℝ)
    (hφ : enorm φ < 2*π) (hr : rotate (rotationExp φ) r₀ = r₀) :
    groupExp (rightLog φ c b ε) * nominal r₀ c b =
      actual (rotationExp φ) ε r₀ c b := by
  rw [rightLog_exp _ _ _ _ hφ, ← right_error _ _ _ _ _ hr]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

theorem jacobian_contraction (φ q : Vec3) (hφ : enorm φ < 2*π) :
    enorm (Jacobian.leftAt φ q) ≤ enorm q := by
  by_cases hz : enorm φ = 0
  · rw [(enorm_eq_zero_iff φ).mp hz]
    simp [Jacobian.leftAt]
  · have hp : 0 < enorm φ := lt_of_le_of_ne (enorm_nonneg φ) (Ne.symm hz)
    rw [Jacobian.leftAt_eq φ q hp]
    exact (Jacobian.left_bounds _ _ (Jacobian.unitAxis_unit φ hp) _ hp hφ).2

/-- Applies to every independent member of a logarithmic translation box. -/
theorem box_radius (q : Vec3) {a b d : ℝ} (ha : |q 0| ≤ a)
    (hb : |q 1| ≤ b) (hz : q 2 = 0) (hd : 0 ≤ d) (hab : a^2+b^2 ≤ d^2) :
    enorm q ≤ d := by
  have hqa : (q 0)^2 ≤ a^2 := by nlinarith [sq_abs (q 0), abs_nonneg (q 0)]
  have hqb : (q 1)^2 ≤ b^2 := by nlinarith [sq_abs (q 1), abs_nonneg (q 1)]
  have hn := enorm_sq q
  simp only [lengthSq, hz, sq, mul_zero, add_zero] at hn
  nlinarith [enorm_nonneg q]

theorem mapped_box_near_rotated_nominal (φ q c r₀ b : Vec3)
    (hφ : enorm φ < 2*π) (hr : rotate (rotationExp φ) r₀ = r₀)
    {a d h : ℝ} (hqa : |q 0| ≤ a) (hqb : |q 1| ≤ h)
    (hqz : q 2 = 0) (hd : 0 ≤ d) (hab : a^2+h^2 ≤ d^2) :
    enorm ((groupExp (![q,0,φ]) * nominal r₀ c b).pos -
      (r₀+rotate (rotationExp φ) b)) ≤ d := by
  have he : (groupExp (![q,0,φ]) * nominal r₀ c b).pos -
      (r₀+rotate (rotationExp φ) b) = Jacobian.leftAt φ q := by
    simp [groupExp, nominal, rotate_add, hr]
  rw [he]
  exact (jacobian_contraction φ q hφ).trans (box_radius q hqa hqb hqz hd hab)

/-- Half-angle coefficient used by the planar right logarithm. -/
def cotCoefficient (θ : ℝ) : ℝ := if θ = 0 then 1 else (θ/2)*cos (θ/2)/sin (θ/2)

theorem cotCoefficient_even (θ : ℝ) : cotCoefficient (-θ) = cotCoefficient θ := by
  by_cases h : θ = 0
  · simp [h, cotCoefficient]
  · simp [cotCoefficient, h, neg_div, sin_neg, cos_neg]
    ring

theorem cotCoefficient_bounds {θ : ℝ} (hθ : |θ| < π) :
    0 ≤ cotCoefficient θ ∧ cotCoefficient θ ≤ 1 := by
  have positive {t : ℝ} (ht : 0 < t) (hp : t < π) :
      0 ≤ cotCoefficient t ∧ cotCoefficient t ≤ 1 := by
    have hs : 0 < sin (t/2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hc : 0 ≤ cos (t/2) := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos],by linarith⟩
    have hb := Coefficients.beta_pos t ht hp
    simp only [cotCoefficient, if_neg ht.ne']
    constructor
    · positivity
    · dsimp [Coefficients.beta] at hb
      nlinarith [show t/2*cos (t/2)/sin (t/2) = (t/2)*(cos (t/2)/sin (t/2)) by ring]
  rcases lt_trichotomy θ 0 with h | h | h
  · rw [← cotCoefficient_even θ]
    exact positive (by linarith) (by simpa [abs_of_neg h] using hθ)
  · simp [h, cotCoefficient]
  · exact positive h (by simpa [abs_of_pos h] using hθ)

theorem right_log_box {θ ε L α e : ℝ} (hθ : |θ| ≤ α) (hα : α < π)
    (hε : |ε| ≤ e) (hL : 0 ≤ L) :
    |ε*L*cotCoefficient θ| ≤ e*L ∧ |ε*L*θ/2| ≤ e*L*α/2 := by
  have ha : 0 ≤ α := (abs_nonneg θ).trans hθ
  have he : 0 ≤ e := (abs_nonneg ε).trans hε
  obtain ⟨hc,hc1⟩ := cotCoefficient_bounds (hθ.trans_lt hα)
  rw [abs_mul, abs_mul, abs_of_nonneg hL, abs_of_nonneg hc]
  constructor
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hε hL) hc).trans (by
        simpa using mul_le_mul_of_nonneg_left hc1 (mul_nonneg he hL))
  · rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hL]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact div_le_div_of_nonneg_right (mul_le_mul
      (mul_le_mul_of_nonneg_right hε hL) hθ (abs_nonneg θ) (mul_nonneg he hL)) (by norm_num)

/-- Planar half-angle identity behind the stated log coordinates.
The zero-angle case is handled separately by the removable definitions. -/
theorem planar_reconstruction (θ : ℝ) (ht : θ ≠ 0) (hs : sin (θ/2) ≠ 0) :
    (sin θ/θ)*cotCoefficient θ - ((1-cos θ)/θ)*(θ/2) = cos θ ∧
    ((1-cos θ)/θ)*cotCoefficient θ + (sin θ/θ)*(θ/2) = sin θ := by
  simp only [cotCoefficient, if_neg ht]
  rw [Jacobian.half_sin θ, Jacobian.half_cos θ]
  constructor <;> field_simp
  · nlinarith [sin_sq_add_cos_sq (θ/2)]
  · ring

/-- A generic closing radius for a gravity-free relative predictor.
S bounds its chief separation, and M=S is the first-exit domain radius. -/
theorem closure_budget {K S T : ℝ} (hK : 0 ≤ K) (hS : 0 < S)
    (hfeedback : K*T^2/2 < 1/2) :
    K*T^2/2 < 1 ∧
    ((K*S)/PreintegrationGravityTransfer.denominator K T)*T^2/2 < S := by
  have hden : 0 < PreintegrationGravityTransfer.denominator K T := by
    unfold PreintegrationGravityTransfer.denominator
    linarith
  constructor
  · linarith
  · rw [show ((K*S)/PreintegrationGravityTransfer.denominator K T)*T^2/2 =
        (S*(K*T^2/2))/PreintegrationGravityTransfer.denominator K T by ring]
    apply (div_lt_iff₀ hden).mpr
    unfold PreintegrationGravityTransfer.denominator
    nlinarith [mul_pos hS (show 0 < 1-K*T^2 by nlinarith)]

def geoK : ℝ := 2*398600441800000/(42164000-2201)^3
def geoBudget : ℝ := (geoK*(2201/2))/(1-geoK*100^2/2)*100^2/2

/-- SI record: r0=1000m, Lmax=100.5m, horizon=100s.
The 59mm upper value is an outward reporting bound, not a chosen allowance. -/
theorem geo_budget_checked : 0 < geoK ∧ geoK*100^2/2 < 1/2 ∧
    0 < geoBudget ∧ geoBudget < 59/1000 := by
  norm_num [geoK, geoBudget]

end GNC.PointingBox
