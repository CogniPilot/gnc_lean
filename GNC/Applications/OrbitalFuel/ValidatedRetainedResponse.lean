import GNC.Applications.OrbitalFuel.ValidatedRetainedPrefix
import GNC.Applications.OrbitalFuel.RetainedPrefixForward
import GNC.Applications.OrbitalFuel.RetainedPrefixPhysics
import GNC.Analysis.EuclideanBox

/-! Continuous response envelopes after applying the actual forward
transition to the accumulated forcing. RetainedResponseIdentity and
ValidatedPhysicalRetained identify this representation with the physical
switched integrals and charge the exact initial root. The transported
nonlinear gravity remainder is not included in this response.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.ValidatedRetainedResponse
open GNC GNC.ThrustSupport RetainedPrefix PolynomialBurn Matrix

def column (x : Trajectory) (n : Fin 68) (t : ℝ) (i : Fin 6) (k : Fin 4) : ℝ :=
  (matrixValue (x.state t) *ᵥ (fun r => ValidatedRetainedPrefix.accumulated x n.val t r k)) i

def response (x : Trajectory) (n : Fin 68) (t : ℝ) (q : Vec3) (j : Fin 2) : Vec3 :=
  fun i => combine (column x n t ⟨3*j.val+i.val,by omega⟩) q

theorem column_error (x : Trajectory) (n : Fin 68) {t : ℝ}
    (ht : t ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (i : Fin 6) (k : Fin 4) :
    |column x n t i k-
      PolynomialAccumulation.value (output (RetainedNormData.pieces n) i k)
        ((RetainedNormData.pieces n).offset:ℝ) t| ≤ 3/10^13 := by
  have h := (RetainedPrefixData.pieces n).forward_transfer (RetainedNormData.pieces n)
    (RetainedPrefixData.valid n) (RetainedNormData.valid n) x
    (fun r => ValidatedRetainedPrefix.accumulated x n.val t r k) i k ht
    (fun r => ValidatedRetainedPrefix.enclosure x n ht r k)
  exact h.trans (by norm_num)

theorem unit_coordinate (q : Vec3) (hq : q ⬝ᵥ q = 1) (i : Fin 3) : |q i| ≤ 1 := by
  have hs : q 0^2+q 1^2+q 2^2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using hq
  apply (sq_le_one_iff_abs_le_one _).mp
  fin_cases i
  · change q 0^2 ≤ 1
    nlinarith [sq_nonneg (q 1), sq_nonneg (q 2)]
  · change q 1^2 ≤ 1
    nlinarith [sq_nonneg (q 0), sq_nonneg (q 2)]
  · change q 2^2 ≤ 1
    nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]

theorem combine_error (a b : Fin 4 → ℝ) (q : Vec3) {ε : ℝ}
    (hq : q ⬝ᵥ q = 1) (he : ∀ k, |a k-b k| ≤ ε) :
    |combine a q-combine b q| ≤ 4*ε := by
  have hq0 := unit_coordinate q hq 0
  have hq1 := unit_coordinate q hq 1
  have hq2 := unit_coordinate q hq 2
  have h0 := mul_le_mul hq0 (he 1) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have h1 := mul_le_mul hq1 (he 2) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have h2 := mul_le_mul hq2 (he 3) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hs : combine a q-combine b q =
      (a 0-b 0)+q 0*(a 1-b 1)+q 1*(a 2-b 2)+q 2*(a 3-b 3) := by unfold combine; ring
  rw [hs]
  have ha := abs_add_le (a 0-b 0) (q 0*(a 1-b 1))
  have hb := abs_add_le ((a 0-b 0)+q 0*(a 1-b 1)) (q 1*(a 2-b 2))
  have hc := abs_add_le ((a 0-b 0)+q 0*(a 1-b 1)+q 1*(a 2-b 2)) (q 2*(a 3-b 3))
  rw [abs_mul] at ha hb hc
  linarith [he 0]

theorem response_error (x : Trajectory) (n : Fin 68) {t : ℝ}
    (ht : t ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (q : Vec3) (hq : q ⬝ᵥ q = 1) (j : Fin 2) :
    GNC.enorm (response x n t q j-(RetainedNormData.pieces n).response j t q) ≤ 4/10^12 := by
  apply enorm_le_of_component_bounds _ (fun _ => (2/10^12:ℝ))
  · intro i
    have h := combine_error (column x n t ⟨3*j.val+i.val,by omega⟩)
      (fun k => PolynomialAccumulation.value
        (output (RetainedNormData.pieces n) ⟨3*j.val+i.val,by omega⟩ k)
        ((RetainedNormData.pieces n).offset:ℝ) t) q hq
      (fun k => column_error x n ht ⟨3*j.val+i.val,by omega⟩ k)
    have hj : (3*j.val+i.val)/3 = j.val := by omega
    have hi : (3*j.val+i.val)%3 = i.val := by omega
    have he (k : Fin 4) : output (RetainedNormData.pieces n) ⟨3*j.val+i.val,by omega⟩ k =
        (RetainedNormData.pieces n).columns j k i := by
      simp only [output]
      congr 1 <;> apply Fin.ext <;> assumption
    simp_rw [he] at h
    change |response x n t q j i-(RetainedNormData.pieces n).response j t q i| ≤ _
    change |response x n t q j i-(RetainedNormData.pieces n).response j t q i| ≤ _ at h
    exact h.trans (by norm_num)
  · norm_num
  · norm_num [Fin.sum_univ_succ]

/-- Exact reference/transition-dependent response envelopes, with the
coefficient, integration and transition errors included. Physical integral
and initial-root transfer are proved downstream in ValidatedPhysicalRetained.
Full nonlinear closure still needs the transported gravity reserve.
The bounds include nominal approach motion. -/
theorem enclosure (x : Trajectory) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (3/5)) (q : Vec3)
    (hq : q ∈ Cap pointingAxis (RetainedNorm.kappa:ℝ)) :
    ∃ n : Fin 68, t ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ) ∧
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) • response x n t q 0) ≤ 10123001 ∧
      GNC.enorm ((RetainedNorm.speedUpper:ℝ) • response x n t q 1) ≤ 5120001/1000000 := by
  obtain ⟨n,hn⟩ := RetainedNormData.coverage ht
  have hb (j : Fin 2) := (RetainedNormData.pieces n).enclosure (RetainedNormData.valid n) j hn q hq
  have he (j : Fin 2) := response_error x n hn q hq.1 j
  have hnorm (j : Fin 2) : GNC.enorm (response x n t q j) ≤
      GNC.enorm ((RetainedNormData.pieces n).response j t q)+4/10^12 := by
    have h := GNC.enorm_add_le (response x n t q j-(RetainedNormData.pieces n).response j t q)
      ((RetainedNormData.pieces n).response j t q)
    rw [sub_add_cancel] at h
    linarith [he j]
  refine ⟨n,hn,?_,?_⟩
  · rw [GNC.enorm_smul,abs_of_nonneg (by norm_num [RetainedNorm.lengthScale])]
    have h := mul_le_mul_of_nonneg_left (hnorm 0)
      (show (0:ℝ) ≤ (RetainedNorm.lengthScale:ℝ) by norm_num [RetainedNorm.lengthScale])
    have b := hb 0
    norm_num [RetainedNorm.scale, RetainedNorm.bound, RetainedNorm.positionBound,
      RetainedNorm.lengthScale] at b h ⊢
    linarith
  · rw [GNC.enorm_smul,abs_of_nonneg (by norm_num [RetainedNorm.speedUpper])]
    have h := mul_le_mul_of_nonneg_left (hnorm 1)
      (show (0:ℝ) ≤ (RetainedNorm.speedUpper:ℝ) by norm_num [RetainedNorm.speedUpper])
    have b := hb 1
    norm_num [RetainedNorm.scale, RetainedNorm.bound, RetainedNorm.velocityBound,
      RetainedNorm.speedUpper] at b h ⊢
    linarith

theorem enclosure_si (x : Trajectory) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (3/5)) (q : Vec3)
    (hq : q ∈ Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) :
    ∃ n : Fin 68, t ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ) ∧
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) • response x n t q 0) ≤ 10123001 ∧
      GNC.enorm (SolarSensitivityFuel.speed • response x n t q 1) ≤ 5120001/1000000 := by
  have hq' : q ∈ Cap pointingAxis (RetainedNorm.kappa:ℝ) := by
    rw [RetainedNorm.kappa_matches]
    exact hq
  obtain ⟨n,hn,hp,hv⟩ := enclosure x ht q hq'
  refine ⟨n,hn,hp,?_⟩
  rw [GNC.enorm_smul,abs_of_nonneg SolarSensitivityFuel.speed_pos.le]
  rw [GNC.enorm_smul,abs_of_nonneg (by norm_num [RetainedNorm.speedUpper])] at hv
  exact (mul_le_mul_of_nonneg_right RetainedNorm.speed_upper (GNC.enorm_nonneg _)).trans hv

end GNC.Applications.OrbitalFuel.ValidatedRetainedResponse
