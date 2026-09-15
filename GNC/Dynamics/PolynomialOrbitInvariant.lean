import GNC.Dynamics.PolynomialOrbit
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue

/-! The polynomial lift preserves the physical inverse-radius constraint.
The constraint error satisfies a scalar homogeneous linear ODE. Uniqueness
and continuity recover the positive inverse-radius branch exactly.
-/
noncomputable section
set_option autoImplicit false
open Set Matrix
open scoped NNReal
namespace GNC.PolynomialOrbit

def radiusConstraint (z : Fin 5 → ℝ) : ℝ := (z 0^2+z 1^2)*z 4^2-1
def constraintCoefficient (z : Fin 5 → ℝ) : ℝ := -2*z 4^2*(z 0*z 2+z 1*z 3)
def project (z : Fin 5 → ℝ) : Fin 4 → ℝ := ![z 0,z 1,z 2,z 3]

theorem constraint_derivative {z : ℝ → Fin 5 → ℝ} {a t : ℝ}
    (hz : HasDerivAt z (rate a (z t)) t) :
    HasDerivAt (fun s => radiusConstraint (z s))
      (constraintCoefficient (z t)*radiusConstraint (z t)) t := by
  have h0 := hasDerivAt_pi.mp hz 0
  have h1 := hasDerivAt_pi.mp hz 1
  have h4 := hasDerivAt_pi.mp hz 4
  convert (((h0.pow 2).add (h1.pow 2)).mul (h4.pow 2)).sub_const 1 using 1
  simp [radiusConstraint, constraintCoefficient, rate]
  ring

theorem constraint_preserved (z : ℝ → Fin 5 → ℝ) (hz : Continuous z) {a T : ℝ}
    (hd : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt z (rate a (z t)) t)
    (hi : radiusConstraint (z 0) = 0) : ∀ t ∈ Icc (0:ℝ) T, radiusConstraint (z t) = 0 := by
  let c := fun t => constraintCoefficient (z t)
  have hc : Continuous c := by unfold c constraintCoefficient; fun_prop
  have he : Continuous (fun t => radiusConstraint (z t)) := by unfold radiusConstraint; fun_prop
  obtain ⟨M,hM,hbound⟩ := (isCompact_Icc.image hc).isBounded.exists_pos_norm_le
  let K : ℝ≥0 := ⟨M,hM.le⟩
  have hlip (t : ℝ) (ht : t ∈ Ico (0:ℝ) T) :
      LipschitzOnWith K (fun u : ℝ => c t*u) univ := by
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [Real.dist_eq, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound (c t) ⟨t,Ico_subset_Icc_self ht,rfl⟩) (abs_nonneg _)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun t u => c t*u) (s := fun _ => univ)
    hlip he.continuousOn
    (fun t ht => (constraint_derivative (hd t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
    (fun _ _ => mem_univ _) continuousOn_const
    (fun t _ => by simpa using (hasDerivAt_const t (0:ℝ)).hasDerivWithinAt)
    (fun _ _ => mem_univ _) hi

theorem radius_pos_of_constraint {z : Fin 5 → ℝ} (h : radiusConstraint z = 0) :
    0 < radius (project z) := by
  have hn : z 0^2+z 1^2 ≠ 0 := by
    intro he
    simp [radiusConstraint, he] at h
  apply Real.sqrt_pos.mpr
  change 0 < z 0^2+z 1^2
  exact lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hn)

theorem inverse_ne_zero_of_constraint {z : Fin 5 → ℝ} (h : radiusConstraint z = 0) : z 4 ≠ 0 := by
  intro he
  simp [radiusConstraint, he] at h

theorem inverse_pos_on (z : ℝ → Fin 5 → ℝ) (hz : Continuous z) {T : ℝ}
    (hi : 0 < z 0 4) (hc : ∀ t ∈ Icc (0:ℝ) T, radiusConstraint (z t) = 0) :
    ∀ t ∈ Icc (0:ℝ) T, 0 < z t 4 := by
  intro t ht
  by_contra h
  have hle : z t 4 ≤ 0 := le_of_not_gt h
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc' ht.1
    (((continuous_apply 4).comp hz).continuousOn) (show 0 ∈ Icc (z t 4) (z 0 4) from ⟨hle,hi.le⟩)
  exact inverse_ne_zero_of_constraint (hc u ⟨hu.1,hu.2.trans ht.2⟩) he

theorem inverse_eq_of_constraint {z : Fin 5 → ℝ} (hc : radiusConstraint z = 0) (hu : 0 < z 4) :
    z 4 = (radius (project z))⁻¹ := by
  have hr := radius_pos_of_constraint hc
  have hs : (radius (project z))^2 = z 0^2+z 1^2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have he : radius (project z)*z 4 = 1 := by
    have hp := mul_pos hr hu
    dsimp [radiusConstraint] at hc
    nlinarith [sq_nonneg (radius (project z)*z 4-1)]
  apply (mul_left_cancel₀ (ne_of_gt hr))
  rw [he, mul_inv_cancel₀ (ne_of_gt hr)]

theorem project_derivative {z : ℝ → Fin 5 → ℝ} {a t : ℝ}
    (hz : HasDerivAt z (rate a (z t)) t)
    (hc : radiusConstraint (z t) = 0) (hu : 0 < z t 4) :
    HasDerivAt (fun s => project (z s)) (physicalRate a (project (z t))) t := by
  have hinv := inverse_eq_of_constraint hc hu
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [project, physicalRate, rate] using hasDerivAt_pi.mp hz 0
  · simpa [project, physicalRate, rate] using hasDerivAt_pi.mp hz 1
  · convert hasDerivAt_pi.mp hz 2 using 1
    simp [project, physicalRate, rate, hinv, div_eq_mul_inv]
    ring
  · convert hasDerivAt_pi.mp hz 3 using 1
    simp [project, physicalRate, rate, hinv, div_eq_mul_inv]
    ring

end GNC.PolynomialOrbit
