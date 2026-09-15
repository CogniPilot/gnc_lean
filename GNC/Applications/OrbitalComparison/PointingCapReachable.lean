import GNC.Analysis.CertifiedImage
import GNC.Applications.OrbitalComparison.PointingCapCertificate

/-! Position reachable sets for the complete physical constant-pointing
family. Both directed inclusions use the same physical certificate;
existence discharges the reverse inclusion for every predicted input. -/
namespace GNC.OrbitalComparison.PointingCapCertificate
open SpatialBurn PointingCapBurn Set
noncomputable section

def Data.pointingSet (D : Data) : Set (Fin 3 → ℝ) :=
  {x | Admissible (D.sigma:ℝ) x}

def Data.positionsFor (D : Data) (t : ℝ) (x : Fin 3 → ℝ) : Set E3 :=
  {z | ∃ X : Motion (D.alpha:ℝ) (direction x), X.p t = z}

def Data.reachablePositions (D : Data) (t : ℝ) : Set E3 :=
  CertifiedImage.family D.pointingSet (D.positionsFor t)

def Data.predictedPositions (D : Data) (t : ℝ) : Set E3 :=
  (fun x => D.position x t) '' D.pointingSet

/-- Changing the approximation leaves the compared physical family fixed
when duration and pointing cap are unchanged. -/
theorem Data.reachablePositions_eq {D₁ D₂ : Data}
    (ha : D₁.alpha = D₂.alpha) (hs : D₁.sigma = D₂.sigma) (t : ℝ) :
    D₁.reachablePositions t = D₂.reachablePositions t := by
  let F (a s : ℚ) : Set E3 :=
    {z | ∃ x, Admissible (s:ℝ) x ∧ ∃ X : Motion (a:ℝ) (direction x), X.p t = z}
  change F D₁.alpha D₁.sigma = F D₂.alpha D₂.sigma
  rw [ha, hs]

theorem Data.positionsFor_nonempty (D : Data) (h : D.Valid)
    (t : ℝ) (x : Fin 3 → ℝ) (hx : x ∈ D.pointingSet) :
    (D.positionsFor t x).Nonempty :=
  ⟨(D.trajectory h x hx).p t, D.trajectory h x hx, rfl⟩

theorem Data.position_set_error (D : Data) (h : D.Valid)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : Fin 3 → ℝ)
    (hx : x ∈ D.pointingSet) (z : E3) (hz : z ∈ D.positionsFor t x) :
    dist z (D.position x t) ≤ (D.positionError:ℝ) := by
  obtain ⟨X, rfl⟩ := hz
  simpa only [dist_eq_norm] using (D.certifies h hx X t ht).1

theorem Data.positionError_nonnegative (D : Data) (h : D.Valid) :
    0 ≤ (D.positionError:ℝ) := by
  have hg := h.gain_nonnegative
  have hd : 0 ≤ 56-D.gain := sub_nonneg.mpr h.gain_max.le
  have hb : 0 ≤ HarmonicCertificate.positionGain D.gain := by
    unfold HarmonicCertificate.positionGain
    positivity
  exact_mod_cast mul_nonneg h.defect_nonnegative hb

theorem Data.position_set_enclosures (D : Data) (h : D.Valid)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    D.reachablePositions t ⊆ CertifiedImage.ballEnvelope (D.positionError:ℝ) (D.predictedPositions t) ∧
    D.predictedPositions t ⊆ CertifiedImage.ballEnvelope (D.positionError:ℝ) (D.reachablePositions t) :=
  CertifiedImage.correspondence D.pointingSet (D.positionsFor t) (fun x => D.position x t)
    (D.positionError:ℝ) (D.positionsFor_nonempty h t) (D.position_set_error h ht)

theorem Data.position_hausdorff (D : Data) (h : D.Valid)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Metric.hausdorffDist (D.reachablePositions t) (D.predictedPositions t) ≤
      (D.positionError:ℝ) :=
  CertifiedImage.hausdorff_bound D.pointingSet (D.positionsFor t) (fun x => D.position x t)
    (D.positionError_nonnegative h) (D.positionsFor_nonempty h t) (D.position_set_error h ht)

theorem Data.position_clearance (D : Data) (h : D.Valid)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (obstacle : Set E3)
    (hclear : ∀ x ∈ D.pointingSet, ∀ z ∈ obstacle,
      (D.positionError:ℝ) < dist (D.position x t) z) :
    Disjoint (D.reachablePositions t) obstacle :=
  CertifiedImage.avoids D.pointingSet (D.positionsFor t) (fun x => D.position x t)
    (D.positionError:ℝ) (D.position_set_error h ht) obstacle hclear

end
end GNC.OrbitalComparison.PointingCapCertificate
