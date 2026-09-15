import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Transfer a uniform physical-prediction certificate to a set enclosure.
The physical family may be specified by a relation, with existence checked
separately. No continuity or finite sampling premise replaces that existence. -/
namespace GNC.CertifiedImage
open Set

variable {ι E : Type*} [PseudoMetricSpace E]

def family (S : Set ι) (F : ι → Set E) : Set E :=
  {z | ∃ i ∈ S, z ∈ F i}

def ballEnvelope (r : ℝ) (S : Set E) : Set E :=
  {z | ∃ y ∈ S, dist z y ≤ r}

theorem correspondence (S : Set ι) (F : ι → Set E) (q : ι → E) (r : ℝ)
    (hex : ∀ i ∈ S, (F i).Nonempty)
    (hbound : ∀ i ∈ S, ∀ z ∈ F i, dist z (q i) ≤ r) :
    (∀ z ∈ family S F, ∃ y ∈ q '' S, dist z y ≤ r) ∧
    (∀ y ∈ q '' S, ∃ z ∈ family S F, dist y z ≤ r) := by
  constructor
  · rintro z ⟨i, hi, hz⟩
    exact ⟨q i, ⟨i, hi, rfl⟩, hbound i hi z hz⟩
  · rintro y ⟨i, hi, rfl⟩
    obtain ⟨z, hz⟩ := hex i hi
    exact ⟨z, ⟨i, hi, hz⟩, by simpa only [dist_comm] using hbound i hi z hz⟩

theorem hausdorff_bound (S : Set ι) (F : ι → Set E) (q : ι → E)
    {r : ℝ} (hr : 0 ≤ r)
    (hex : ∀ i ∈ S, (F i).Nonempty)
    (hbound : ∀ i ∈ S, ∀ z ∈ F i, dist z (q i) ≤ r) :
    Metric.hausdorffDist (family S F) (q '' S) ≤ r := by
  obtain ⟨h₁, h₂⟩ := correspondence S F q r hex hbound
  exact Metric.hausdorffDist_le_of_mem_dist hr h₁ h₂

theorem avoids (S : Set ι) (F : ι → Set E) (q : ι → E) (r : ℝ)
    (hbound : ∀ i ∈ S, ∀ z ∈ F i, dist z (q i) ≤ r)
    (obstacle : Set E)
    (hclear : ∀ i ∈ S, ∀ z ∈ obstacle, r < dist (q i) z) :
    Disjoint (family S F) obstacle := by
  apply Set.disjoint_left.mpr
  rintro z ⟨i, hi, hz⟩ ho
  exact not_le_of_gt (hclear i hi z ho) (by simpa only [dist_comm] using hbound i hi z hz)

/-- Equal reachable images can have arbitrarily large error at matched
parameter labels. A pointwise lower bound is not a set-distance lower bound. -/
theorem relabeling_gap (a : ℝ) (ha : 0 ≤ a) :
    Metric.hausdorffDist (id '' Icc (-a) a) ((fun x : ℝ => -x) '' Icc (-a) a) = 0 ∧
      dist (id a) (-a) = 2*a := by
  have h : (fun x : ℝ => -x) '' Icc (-a) a = Icc (-a) a := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      constructor <;> linarith [hy.1, hy.2]
    · intro hx
      exact ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, neg_neg x⟩
  constructor
  · simp [h]
  · change dist a (-a) = 2*a
    rw [Real.dist_eq, sub_neg_eq_add, abs_of_nonneg (add_nonneg ha ha)]
    ring

end GNC.CertifiedImage
