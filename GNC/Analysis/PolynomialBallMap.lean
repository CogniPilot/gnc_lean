import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! An exact cubic parameterization of low-dimensional Euclidean balls.
The map need not be injective: its image of any set between the unit ball
and the radius-two ball is exactly the unit ball. For dimensions at most
four this includes the unit cube. This permits dependency-preserving
polynomial set representations without replacing a disk by an outer box.
-/
noncomputable section
namespace GNC.PolynomialBallMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radial (x : E) : E := ((3 - ‖x‖^2) / 2 : ℝ) • x

theorem norm_square_identity (x : E) :
    1 - ‖radial x‖^2 = (‖x‖^2 - 1)^2 * (4 - ‖x‖^2) / 4 := by
  simp only [radial, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem norm_radial_le_one {x : E} (hx : ‖x‖ ≤ 2) : ‖radial x‖ ≤ 1 := by
  have hs : ‖x‖^2 ≤ 4 := by nlinarith [norm_nonneg x]
  have hp := mul_nonneg (sq_nonneg (‖x‖^2 - 1)) (sub_nonneg.mpr hs)
  have hi := norm_square_identity x
  nlinarith [norm_nonneg (radial x)]

theorem unit_ball_preimage {y : E} (hy : ‖y‖ ≤ 1) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ radial x = y := by
  by_cases hz : y = 0
  · subst y
    exact ⟨0, by simp, by simp [radial]⟩
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hz
  let h : ℝ → ℝ := fun r => r * (3-r^2)/2
  have hc : Continuous h := by dsimp [h]; fun_prop
  have hm : ‖y‖ ∈ Set.Icc (h 0) (h 1) := by
    norm_num [h]
    exact hy
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num)
    hc.continuousOn hm
  let x : E := (r / ‖y‖ : ℝ) • y
  have hn : ‖x‖ = r := by
    simp only [x, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hr.1 hpos.le)]
    exact div_mul_cancel₀ r hpos.ne'
  refine ⟨x, hn ▸ hr.2, ?_⟩
  rw [radial, hn]
  change ((3-r^2)/2 : ℝ) • ((r/‖y‖ : ℝ) • y) = y
  rw [smul_smul]
  have hs : (3-r^2)/2 * (r/‖y‖) = 1 := by
    dsimp [h] at he
    field_simp
    nlinarith
  rw [hs, one_smul]

theorem image_eq_unit_ball {S : Set E}
    (hinner : Metric.closedBall 0 1 ⊆ S)
    (houter : S ⊆ Metric.closedBall 0 2) :
    radial '' S = Metric.closedBall 0 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at *
    exact norm_radial_le_one (by simpa using houter hx)
  · intro y hy
    simp only [Metric.mem_closedBall, dist_zero_right] at hy
    obtain ⟨x, hx, he⟩ := unit_ball_preimage hy
    exact ⟨x, hinner (by simpa using hx), he⟩

variable {ι : Type*} [Fintype ι]

def cube : Set (EuclideanSpace ℝ ι) := {x | ∀ i, |x i| ≤ 1}

theorem radial_apply (x : EuclideanSpace ℝ ι) (i : ι) :
    radial x i = (3 - ∑ j, (x j)^2) / 2 * x i := by
  simp only [radial, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.real_norm_sq_eq]

theorem cube_image (hd : Fintype.card ι ≤ 4) :
    radial '' (cube : Set (EuclideanSpace ℝ ι)) = Metric.closedBall 0 1 := by
  apply image_eq_unit_ball
  · intro x hx i
    have h := PiLp.norm_apply_le x i
    have hn : ‖x‖ ≤ 1 := by simpa using hx
    simpa using h.trans hn
  · intro x hx
    have hs : ‖x‖^2 ≤ 4 := calc
      _ = ∑ i, (x i)^2 := EuclideanSpace.real_norm_sq_eq x
      _ ≤ ∑ _i : ι, (1:ℝ) := Finset.sum_le_sum fun i _ => by
        have h := abs_le.mp (hx i)
        nlinarith [sq_nonneg (x i)]
      _ = (Fintype.card ι : ℝ) := by simp
      _ ≤ 4 := by exact_mod_cast hd
    have hn : ‖x‖ ≤ 2 := by nlinarith [norm_nonneg x]
    simpa using hn

/-- The two coordinate cubics, with arguments interchanged for the second. -/
def diskX (a b : ℝ) : ℝ := a * (3-a^2-b^2) / 2

theorem disk_inside {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    diskX a b ^ 2 + diskX b a ^ 2 ≤ 1 := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hs : a^2+b^2 ≤ 2 := by nlinarith
  have hp := mul_nonneg (sq_nonneg (a^2+b^2-1)) (show 0 ≤ 4-(a^2+b^2) by linarith)
  have hi : 1-(diskX a b ^ 2 + diskX b a ^ 2) =
      (a^2+b^2-1)^2*(4-(a^2+b^2))/4 := by unfold diskX; ring
  nlinarith

theorem disk_surjective {u v : ℝ} (h : u^2+v^2 ≤ 1) :
    ∃ a b : ℝ, |a| ≤ 1 ∧ |b| ≤ 1 ∧ diskX a b = u ∧ diskX b a = v := by
  let y : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![u,v]
  have hy : y ∈ Metric.closedBall 0 1 := by
    have hs : ‖y‖^2 = u^2+v^2 := by
      simp [EuclideanSpace.real_norm_sq_eq, y, Fin.sum_univ_two]
    have hn : ‖y‖ ≤ 1 := by nlinarith [norm_nonneg y]
    simpa using hn
  rw [← cube_image (ι := Fin 2) (by decide)] at hy
  obtain ⟨x, hx, he⟩ := hy
  refine ⟨x 0, x 1, hx 0, hx 1, ?_, ?_⟩
  · have hi := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) he
    simp only [radial_apply, Fin.sum_univ_two] at hi
    dsimp [y] at hi
    dsimp [diskX]
    nlinarith
  · have hi := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) he
    simp only [radial_apply, Fin.sum_univ_two] at hi
    dsimp [y] at hi
    dsimp [diskX]
    nlinarith

theorem scaled_disk_inside (σ : ℝ) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    (σ*diskX a b)^2+(σ*diskX b a)^2 ≤ σ^2 := by
  have h := mul_le_mul_of_nonneg_left (disk_inside ha hb) (sq_nonneg σ)
  nlinarith

theorem scaled_disk_surjective {σ u v : ℝ} (hσ : 0 < σ) (h : u^2+v^2 ≤ σ^2) :
    ∃ a b : ℝ, |a| ≤ 1 ∧ |b| ≤ 1 ∧ σ*diskX a b = u ∧ σ*diskX b a = v := by
  have hn : (u/σ)^2+(v/σ)^2 ≤ 1 := by
    rw [div_pow, div_pow, ← add_div]
    exact (div_le_one (sq_pos_of_pos hσ)).mpr h
  obtain ⟨a,b,ha,hb,hu,hv⟩ := disk_surjective hn
  refine ⟨a,b,ha,hb,?_,?_⟩
  · rw [hu, mul_div_cancel₀ _ hσ.ne']
  · rw [hv, mul_div_cancel₀ _ hσ.ne']

end GNC.PolynomialBallMap
