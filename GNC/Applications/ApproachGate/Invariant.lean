import GNC.Applications.ApproachGate.Model

/-! Preservation of the inverse-radius and rotation-phase constraints.
These results connect solutions of the polynomial lift back to physical
inverse-square motion; the auxiliary states are not independent dynamics.
-/
noncomputable section
namespace GNC.ApproachGate
open Set Matrix

theorem constant_on_interval {f : ℝ → ℝ} {T : ℝ}
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt f 0 t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : f t = f 0 := by
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hd s ⟨hs.1, hs.2.trans ht.2⟩).hasDerivWithinAt)
    (fun s (_ : s ∈ Ico (0 : ℝ) t) => by norm_num :
      ∀ s ∈ Ico (0 : ℝ) t, ‖(0 : ℝ)‖ ≤ (0 : ℝ))
    t (right_mem_Icc.mpr ht.1)
  simpa only [sub_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using hm

def project (z : Fin 11 → ℝ) : Fin 6 → ℝ := ![z 0,z 1,z 2,z 3,z 4,z 5]

def inverseDefect (z : Fin 11 → ℝ) : ℝ :=
  ((z 6+1)⁻¹)^2-((1+z 0)^2+z 1^2+z 2^2)

theorem inverse_defect_derivative {z : ℝ → Fin 11 → ℝ} {t : ℝ}
    {mode : Law} {u : Fin 2 → ℝ}
    (hz : HasDerivAt z (rate mode u (z t)) t) (hU : z t 6+1 ≠ 0) :
    HasDerivAt (fun s => inverseDefect (z s)) 0 t := by
  have h0 := hasDerivAt_pi.mp hz 0
  have h1 := hasDerivAt_pi.mp hz 1
  have h2 := hasDerivAt_pi.mp hz 2
  have h6 := hasDerivAt_pi.mp hz 6
  convert (((h6.add_const 1).inv hU).pow 2).sub
    ((((h0.const_add 1).pow 2).add (h1.pow 2)).add (h2.pow 2)) using 1
  simp [rate]
  field_simp
  <;> ring

theorem inverse_constraint {z : ℝ → Fin 11 → ℝ} {T : ℝ}
    {mode : Law} {u : Fin 2 → ℝ}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt z (rate mode u (z t)) t)
    (hU : ∀ t ∈ Icc (0 : ℝ) T, 0 < z t 6+1)
    (hi : inverseDefect (z 0) = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    0 < CircularRendezvous3D.radius (project (z t)) ∧
      z t 6+1 = (CircularRendezvous3D.radius (project (z t)))⁻¹ := by
  have hc := constant_on_interval
    (fun s hs => inverse_defect_derivative (hz s hs) (ne_of_gt (hU s hs))) ht
  rw [hi] at hc
  have he : ((z t 6+1)⁻¹)^2 = (1+z t 0)^2+z t 1^2+z t 2^2 := by
    exact sub_eq_zero.mp hc
  have hr : CircularRendezvous3D.radius (project (z t)) = (z t 6+1)⁻¹ := by
    change Real.sqrt ((1+z t 0)^2+z t 1^2+z t 2^2) = _
    rw [← he, Real.sqrt_sq (inv_pos.mpr (hU t ht)).le]
  rw [hr, inv_inv]
  exact ⟨inv_pos.mpr (hU t ht), rfl⟩

def phaseDefect (phase : ℝ) (z : Fin 11 → ℝ) : ℝ :=
  (z 9-Real.cos phase)^2+(z 10-Real.sin phase)^2

theorem phase_defect_derivative {z : ℝ → Fin 11 → ℝ} {t start : ℝ}
    {mode : Law} {u : Fin 2 → ℝ}
    (hz : HasDerivAt z (rate mode u (z t)) t) :
    HasDerivAt (fun s => phaseDefect (start+s) (z s)) 0 t := by
  have hc := ((hasDerivAt_pi.mp hz 9).sub ((hasDerivAt_id t).const_add start).cos).pow 2
  have hs := ((hasDerivAt_pi.mp hz 10).sub ((hasDerivAt_id t).const_add start).sin).pow 2
  convert hc.add hs using 1
  simp [rate]
  ring

theorem phase_constraint {z : ℝ → Fin 11 → ℝ} {T start : ℝ}
    {mode : Law} {u : Fin 2 → ℝ}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt z (rate mode u (z t)) t)
    (hi : phaseDefect start (z 0) = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    z t 9 = Real.cos (start+t) ∧ z t 10 = Real.sin (start+t) := by
  have h := constant_on_interval (fun s hs => phase_defect_derivative (start := start) (hz s hs)) ht
  simp only [add_zero, hi] at h
  change (z t 9-Real.cos (start+t))^2+(z t 10-Real.sin (start+t))^2 = 0 at h
  constructor <;> nlinarith [sq_nonneg (z t 9-Real.cos (start+t)),
    sq_nonneg (z t 10-Real.sin (start+t))]

theorem pointing_constraint {z : ℝ → Fin 11 → ℝ} {T : ℝ}
    {mode : Law} {u : Fin 2 → ℝ}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt z (rate mode u (z t)) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    z t 7 = z 0 7 ∧ z t 8 = z 0 8 := by
  constructor
  · exact constant_on_interval (fun s hs => by simpa [rate] using hasDerivAt_pi.mp (hz s hs) 7) ht
  · exact constant_on_interval (fun s hs => by simpa [rate] using hasDerivAt_pi.mp (hz s hs) 8) ht

theorem project_derivative {z : ℝ → Fin 11 → ℝ} {t θ phase : ℝ}
    {mode : Law} {u : Fin 2 → ℝ}
    (hz : HasDerivAt z (rate mode u (z t)) t)
    (hU : z t 6+1 = (CircularRendezvous3D.radius (project (z t)))⁻¹)
    (hs : z t 7 = Real.sin θ) (hc : z t 8 = 1-Real.cos θ)
    (hC : z t 9 = Real.cos phase) (hS : z t 10 = Real.sin phase) :
    HasDerivAt (fun s => project (z s))
      (CircularRendezvous3D.physicalRate (source mode θ phase u) (project (z t))) t := by
  have he : z t 6 = (CircularRendezvous3D.radius (project (z t)))⁻¹-1 := by linarith
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [project, rate, CircularRendezvous3D.physicalRate] using hasDerivAt_pi.mp hz 0
  · simpa [project, rate, CircularRendezvous3D.physicalRate] using hasDerivAt_pi.mp hz 1
  · simpa [project, rate, CircularRendezvous3D.physicalRate] using hasDerivAt_pi.mp hz 2
  · convert hasDerivAt_pi.mp hz 3 using 1
    simp [project, rate, CircularRendezvous3D.physicalRate, source_components,
      hs, hc, hC, hS, he, div_eq_mul_inv]
    ring
  · convert hasDerivAt_pi.mp hz 4 using 1
    simp [project, rate, CircularRendezvous3D.physicalRate, source_components,
      hs, hc, hC, hS, he, div_eq_mul_inv]
    ring
  · convert hasDerivAt_pi.mp hz 5 using 1
    simp [project, rate, CircularRendezvous3D.physicalRate, source_components,
      hs, hc, hC, hS, he, div_eq_mul_inv]
    ring_nf
    simp

end GNC.ApproachGate
