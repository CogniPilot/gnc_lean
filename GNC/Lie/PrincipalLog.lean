import GNC.Lie.LocalLog

/-! A smooth principal logarithm on the open image of the principal
rotation ball. Coordinate existence and regularity follow from the inverse
function theorem and principal injectivity. -/
noncomputable section
open Matrix Filter Set
open scoped Matrix ContDiff Manifold Topology
namespace GNC.PrincipalLog

def domain : Set SE23 := {X | ∃ x : LogState, enorm (x 2) < Real.pi ∧ groupExp x = X}

def log (X : SE23) : LogState := by
  classical
  exact if h : X ∈ domain then Classical.choose h else 0

theorem log_spec {X : SE23} (hX : X ∈ domain) :
    enorm (log X 2) < Real.pi ∧ groupExp (log X) = X := by
  simpa only [log, dif_pos hX] using Classical.choose_spec hX

theorem exp_mem_domain (x : LogState) (hx : enorm (x 2) < Real.pi) : groupExp x ∈ domain :=
  ⟨x,hx,rfl⟩

theorem log_exp (x : LogState) (hx : enorm (x 2) < Real.pi) : log (groupExp x) = x := by
  obtain ⟨hθ,he⟩ := log_spec (exp_mem_domain x hx)
  exact groupExp_injective hθ hx he

theorem local_agreement (x : LogState) (hx : enorm (x 2) < Real.pi) :
    ∀ᶠ X in 𝓝 (groupExp x), X ∈ domain ∧
      log X = LocalLog.near x (by linarith [Real.pi_pos]) X := by
  have hx' : enorm (x 2) < 2*Real.pi := by linarith [Real.pi_pos]
  have hb : IsOpen {z : LogState | enorm (z 2) < Real.pi} :=
    isOpen_Iio.preimage (enorm_continuous.comp (continuous_apply 2))
  have hn := (LocalLog.near_contMDiffAt x hx').continuousAt.preimage_mem_nhds
    (show {z : LogState | enorm (z 2) < Real.pi} ∈ 𝓝 (LocalLog.near x hx' (groupExp x)) by
      rw [LocalLog.near_at_exp]; exact hb.mem_nhds hx)
  filter_upwards [LocalLog.exp_near_eventually x hx', hn] with X he hθ
  have hX : X ∈ domain := ⟨LocalLog.near x hx' X,hθ,he⟩
  refine ⟨hX, ?_⟩
  exact groupExp_injective (log_spec hX).1 hθ ((log_spec hX).2.trans he.symm)

theorem isOpen_domain : IsOpen domain := by
  rw [isOpen_iff_mem_nhds]
  rintro X ⟨x,hx,rfl⟩
  exact (local_agreement x hx).mono fun _ h => h.1

theorem log_contMDiffAt {X : SE23} (hX : X ∈ domain) :
    ContMDiffAt 𝓘(ℝ, SE23.Model) 𝓘(ℝ, LogState) ∞ log X := by
  obtain ⟨x,hx,rfl⟩ := hX
  exact (LocalLog.near_contMDiffAt x (by linarith [Real.pi_pos])).congr_of_eventuallyEq
    ((local_agreement x hx).mono fun _ h => h.2)

theorem log_contMDiffOn : ContMDiffOn 𝓘(ℝ, SE23.Model) 𝓘(ℝ, LogState) ∞ log domain :=
  fun _ h => (log_contMDiffAt h).contMDiffWithinAt

/-- A smooth group-error trajectory in the principal domain has a smooth
log lift whose exponential equals the actual trajectory everywhere. -/
theorem smooth_lift {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → SE23)
    (hf : ContMDiff I 𝓘(ℝ, SE23.Model) ∞ f) (hd : ∀ t, f t ∈ domain) :
    ContMDiff I 𝓘(ℝ, LogState) ∞ (fun t => log (f t)) ∧
      (∀ t, groupExp (log (f t)) = f t) := by
  exact ⟨fun t => (log_contMDiffAt (hd t)).comp t (hf t), fun t => (log_spec (hd t)).2⟩

end GNC.PrincipalLog
