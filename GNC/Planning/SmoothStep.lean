import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-! A quintic interpolation with constant extensions. The two joins have
zero first and second derivatives, including derivatives at the joins.
Time scaling is explicit; these bounds concern angle coordinates, not yet
the angular velocity of a composed attitude. -/
noncomputable section
set_option autoImplicit false
namespace GNC.Planning.SmoothStep
open Set Filter
open scoped Topology

def join (a : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ a then f x else g x

theorem join_derivative {f g f' g' : ℝ → ℝ} (a x : ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hv : f a = g a) (hd : f' a = g' a) :
    HasDerivAt (join a f g) (join a f' g' x) x := by
  rcases lt_trichotomy x a with hx | hx | hx
  · rw [join, if_pos hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with t ht
    exact if_pos ht.le
  · subst x
    have hl : HasDerivWithinAt (join a f g) (f' a) (Iic a) a :=
      (hf a).hasDerivWithinAt.congr (fun t ht => if_pos ht) (if_pos le_rfl)
    have hr : HasDerivWithinAt (join a f g) (f' a) (Ici a) a := by
      rw [hd]
      apply (hg a).hasDerivWithinAt.congr
      · intro t ht
        by_cases hta : t ≤ a
        · have he : t = a := le_antisymm hta ht
          subst t
          simpa [join] using hv
        · exact if_neg hta
      · simpa [join] using hv
    simpa [Iic_union_Ici, join] using hl.union hr
  · rw [join, if_neg hx.not_ge]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact if_neg ht.not_ge

theorem join_continuous {f g : ℝ → ℝ} (a : ℝ) (hf : Continuous f)
    (hg : Continuous g) (hv : f a = g a) : Continuous (join a f g) :=
  hf.if_le hg continuous_id continuous_const (fun x hx => by simpa [hx] using hv)

def polynomial (u : ℝ) : ℝ := 10*u^3-15*u^4+6*u^5
def first (u : ℝ) : ℝ := 30*u^2*(1-u)^2
def second (u : ℝ) : ℝ := 60*u*(1-u)*(1-2*u)

def value : ℝ → ℝ := join 0 (fun _ => 0) (join 1 polynomial (fun _ => 1))
def velocity : ℝ → ℝ := join 0 (fun _ => 0) (join 1 first (fun _ => 0))
def acceleration : ℝ → ℝ := join 0 (fun _ => 0) (join 1 second (fun _ => 0))

theorem polynomial_derivative (u : ℝ) : HasDerivAt polynomial (first u) u := by
  unfold polynomial first
  convert (((hasDerivAt_id u).pow 3).const_mul 10 |>.sub
    (((hasDerivAt_id u).pow 4).const_mul 15) |>.add
    (((hasDerivAt_id u).pow 5).const_mul 6)) using 1 <;> dsimp <;> ring

theorem first_derivative (u : ℝ) : HasDerivAt first (second u) u := by
  unfold first second
  convert ((((hasDerivAt_id u).pow 2).const_mul 30).mul
    (((hasDerivAt_const u 1).sub (hasDerivAt_id u)).pow 2)) using 1 <;> dsimp <;> ring

theorem value_derivative (u : ℝ) : HasDerivAt value (velocity u) u := by
  apply join_derivative 0 u (fun t => hasDerivAt_const t 0)
    (fun t => join_derivative 1 t polynomial_derivative (fun s => hasDerivAt_const s 1)
      (by norm_num [polynomial]) (by norm_num [first]))
    <;> norm_num [join, polynomial, first]

theorem velocity_derivative (u : ℝ) : HasDerivAt velocity (acceleration u) u := by
  apply join_derivative 0 u (fun t => hasDerivAt_const t 0)
    (fun t => join_derivative 1 t first_derivative (fun s => hasDerivAt_const s 0)
      (by norm_num [first]) (by norm_num [second]))
    <;> norm_num [join, first, second]

theorem value_continuous : Continuous value :=
  continuous_iff_continuousAt.mpr (fun u => (value_derivative u).continuousAt)

theorem velocity_continuous : Continuous velocity :=
  continuous_iff_continuousAt.mpr (fun u => (velocity_derivative u).continuousAt)

theorem acceleration_continuous : Continuous acceleration := by
  apply join_continuous 0 continuous_const
    (join_continuous 1 (by unfold second; fun_prop) continuous_const (by norm_num [second]))
  norm_num [join, second]

theorem value_before {u : ℝ} (hu : u ≤ 0) : value u = 0 := if_pos hu
theorem value_after {u : ℝ} (hu : 1 ≤ u) : value u = 1 := by
  rcases hu.eq_or_lt with rfl | hu
  · norm_num [value, join, polynomial]
  · simp [value, join, (by linarith : ¬ u ≤ 0), hu.not_ge]

theorem jets_before {u : ℝ} (hu : u ≤ 0) : velocity u = 0 ∧ acceleration u = 0 :=
  ⟨if_pos hu, if_pos hu⟩
theorem jets_after {u : ℝ} (hu : 1 ≤ u) : velocity u = 0 ∧ acceleration u = 0 := by
  rcases hu.eq_or_lt with rfl | hu
  · norm_num [velocity, acceleration, join, first, second]
  · simp [velocity, acceleration, join, (by linarith : ¬ u ≤ 0), hu.not_ge]

theorem velocity_bounds (u : ℝ) : 0 ≤ velocity u ∧ velocity u ≤ 15/8 := by
  by_cases h0 : u ≤ 0
  · rw [(jets_before h0).1]; norm_num
  by_cases h1 : 1 ≤ u
  · rw [(jets_after h1).1]; norm_num
  have hpos : 0 ≤ u*(1-u) := mul_nonneg (by linarith) (by linarith)
  have hmax : u*(1-u) ≤ 1/4 := by nlinarith [sq_nonneg (u-1/2)]
  have hs := mul_nonneg hpos (sub_nonneg.mpr hmax)
  have hb := sq_nonneg (u*(1-u)-1/4)
  simp only [velocity, join, if_neg h0, if_pos (show u ≤ 1 by linarith), first]
  constructor
  · positivity
  · nlinarith [mul_nonneg (sub_nonneg.mpr hmax) (by linarith : 0 ≤ 1/4+u*(1-u))]

theorem acceleration_bound (u : ℝ) : |acceleration u| ≤ 15 := by
  by_cases h0 : u ≤ 0
  · rw [(jets_before h0).2]; norm_num
  by_cases h1 : 1 ≤ u
  · rw [(jets_after h1).2]; norm_num
  have hpos : 0 ≤ u*(1-u) := mul_nonneg (by linarith) (by linarith)
  have hmax : u*(1-u) ≤ 1/4 := by nlinarith [sq_nonneg (u-1/2)]
  have hlin : |1-2*u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [acceleration, join, if_neg h0, if_pos (show u ≤ 1 by linarith), second]
  rw [show 60*u*(1-u)*(1-2*u) = 60*(u*(1-u))*(1-2*u) by ring,
    abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hpos)]
  calc
    _ ≤ 60*(u*(1-u))*1 := mul_le_mul_of_nonneg_left hlin (by positivity)
    _ ≤ 15 := by nlinarith

def blend (a d start finish t : ℝ) : ℝ := start+(finish-start)*value ((t-a)/d)
def blendVelocity (a d start finish t : ℝ) : ℝ :=
  (finish-start)*velocity ((t-a)/d)/d
def blendAcceleration (a d start finish t : ℝ) : ℝ :=
  (finish-start)*acceleration ((t-a)/d)/d^2

theorem blend_derivative (a d start finish t : ℝ) :
    HasDerivAt (blend a d start finish) (blendVelocity a d start finish t) t := by
  have h := (value_derivative ((t-a)/d)).comp t ((hasDerivAt_id t).sub_const a |>.div_const d)
  convert (h.const_mul (finish-start)).const_add start using 1 <;>
    simp [blend, blendVelocity] <;> ring

theorem blendVelocity_derivative (a d start finish t : ℝ) :
    HasDerivAt (blendVelocity a d start finish) (blendAcceleration a d start finish t) t := by
  have h := (velocity_derivative ((t-a)/d)).comp t
    ((hasDerivAt_id t).sub_const a |>.div_const d)
  convert (h.const_mul (finish-start)).div_const d using 1 <;>
    simp [blendVelocity, blendAcceleration] <;> ring

theorem blend_before {a d start finish t : ℝ} (hd : 0 < d) (ht : t ≤ a) :
    blend a d start finish t = start := by
  have he : (t-a)/d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  simp [blend, value_before he]

theorem blend_after {a d start finish t : ℝ} (hd : 0 < d) (ht : a+d ≤ t) :
    blend a d start finish t = finish := by
  rw [blend, value_after ((le_div_iff₀ hd).mpr (by linarith))]
  ring

theorem blendVelocity_bound {a d start finish t : ℝ} (hd : 0 < d) :
    |blendVelocity a d start finish t| ≤ |finish-start| * (15/8)/d := by
  rw [blendVelocity, abs_div, abs_mul, abs_of_pos hd,
    abs_of_nonneg (velocity_bounds _).1]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (velocity_bounds _).2 (abs_nonneg _)) hd.le

theorem blendAcceleration_bound {a d start finish t : ℝ} (hd : 0 < d) :
    |blendAcceleration a d start finish t| ≤ |finish-start| * 15/d^2 := by
  rw [blendAcceleration, abs_div, abs_mul, abs_of_nonneg (sq_nonneg d)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (acceleration_bound _) (abs_nonneg _)) (sq_nonneg d)

end GNC.Planning.SmoothStep
