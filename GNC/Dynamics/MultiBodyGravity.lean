import GNC.Dynamics.GravityPairedError

/-! Point-mass gravity from finitely many moving bodies, including a spatially
uniform acceleration of the coordinate origin. Each body's reference motion
is retained; there is no frozen-center approximation. Shared body-ephemeris
errors enter relative dynamics through a mixed gravity difference. These
theorems do not supply ephemerides or certify a particular mission model.
-/
noncomputable section
open Finset
namespace GNC.Gravity
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι]

def multiField (μ : ι → ℝ) (center : ι → E) (originAcceleration p : E) : E :=
  originAcceleration + ∑ i, field (μ i) (p-center i)

def multiGradient (μ : ι → ℝ) (center : ι → E) (p v : E) : E :=
  ∑ i, gradient (μ i) (p-center i) v

/-- Spatially uniform terms, including an accelerating origin, cancel exactly
between trajectories in the same frame. -/
theorem multiField_difference (μ : ι → ℝ) (center : ι → E) (a p q : E) :
    multiField μ center a p - multiField μ center a q =
      ∑ i, (field (μ i) (p-center i)-field (μ i) (q-center i)) := by
  simp only [multiField, sum_sub_distrib]
  abel

/-- Actual time differentiation includes every moving center's velocity.
The spatial state derivative remains the sum of the individual gradients. -/
theorem multiField_derivative (μ : ι → ℝ) (center : ι → ℝ → E)
    (a p : ℝ → E) (centerVelocity : ι → E) (a' v : E) {t : ℝ}
    (ha : HasDerivAt a a' t) (hp : HasDerivAt p v t)
    (hc : ∀ i, HasDerivAt (center i) (centerVelocity i) t)
    (hne : ∀ i, p t-center i t ≠ 0) :
    HasDerivAt (fun s => multiField μ (fun i => center i s) (a s) (p s))
      (a' + ∑ i, gradient (μ i) (p t-center i t) (v-centerVelocity i)) t := by
  apply ha.add
  simpa only [Pi.sub_apply] using HasDerivAt.fun_sum (u := univ)
    (fun i _ => field_derivative (μ i) (hp.sub (hc i)) (hne i))

/-- The complete multibody Taylor residual is the sum of the individual
inverse-square residuals, on a separately nonsingular region for each body. -/
theorem multiField_remainder [CompleteSpace E]
    (μ : ι → ℝ) (center : ι → E) (a p d : E)
    (hμ : ∀ i, 0 ≤ μ i) (hd : ∀ i, ‖d‖ < ‖p-center i‖) :
    ‖multiField μ center a (p+d)-multiField μ center a p-
      multiGradient μ center p d‖ ≤
        ∑ i, remainderBound (μ i) ‖p-center i‖ ‖d‖ := by
  rw [multiField_difference]
  unfold multiGradient
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  convert remainder_bound (μ i) (hμ i) (p-center i) d (hd i) using 1 <;>
    congr 2 <;> abel

/-- Both the nominal spacecraft error and a common body-ephemeris error are
shared shifts in relative gravity. They may be correlated. The near-linear
bound retains the complete reference gradient and charges the remaining
quadratic, gradient-change and mixed-shift terms separately. -/
theorem multiField_paired_near_linear [CompleteSpace E]
    (μ : ι → ℝ) (referenceCenter actualCenter : ι → E)
    (referenceOrigin actualOrigin q d nominalError relativeError : E)
    (r N : ι → ℝ) (D M : ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hr : ∀ i, 0 < r i)
    (hq : ∀ i, r i+D+N i+M ≤ ‖q-referenceCenter i‖)
    (hd : ‖d‖ ≤ D)
    (hn : ∀ i, ‖nominalError-(actualCenter i-referenceCenter i)‖ ≤ N i)
    (he : ‖relativeError‖ ≤ M) :
    ‖(multiField μ actualCenter actualOrigin (q+d+nominalError+relativeError)-
        multiField μ actualCenter actualOrigin (q+nominalError))-
      (multiField μ referenceCenter referenceOrigin (q+d)-
        multiField μ referenceCenter referenceOrigin q)-
      multiGradient μ referenceCenter q relativeError‖ ≤
      ∑ i, ((3*μ i/(r i)^4)*‖relativeError‖^2+
        (6*μ i/(r i)^4)*(D+N i)*‖relativeError‖+
        (6*μ i/(r i)^4)*‖d‖*‖nominalError-(actualCenter i-referenceCenter i)‖) := by
  rw [multiField_difference, multiField_difference]
  unfold multiGradient
  rw [← sum_sub_distrib, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  have h := paired_field_near_linear (μ i) (hμ i) (q-referenceCenter i) d
    (nominalError-(actualCenter i-referenceCenter i)) relativeError
    (hr i) (hq i) hd (hn i) he
  convert h using 1 <;> congr 2 <;> abel

/-- Without a relative prediction error, the entire shared ephemeris effect
is bilinear in displacement and shared shift. -/
theorem multiField_shared_ephemeris (μ : ι → ℝ)
    (referenceCenter actualCenter : ι → E)
    (referenceOrigin actualOrigin q d nominalError : E)
    (r N : ι → ℝ) (D : ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hr : ∀ i, 0 < r i)
    (hq : ∀ i, r i+D+N i ≤ ‖q-referenceCenter i‖)
    (hd : ‖d‖ ≤ D)
    (hn : ∀ i, ‖nominalError-(actualCenter i-referenceCenter i)‖ ≤ N i) :
    ‖(multiField μ actualCenter actualOrigin (q+d+nominalError)-
        multiField μ actualCenter actualOrigin (q+nominalError))-
      (multiField μ referenceCenter referenceOrigin (q+d)-
        multiField μ referenceCenter referenceOrigin q)‖ ≤
      ∑ i, (6*μ i/(r i)^4)*‖d‖*‖nominalError-(actualCenter i-referenceCenter i)‖ := by
  rw [multiField_difference, multiField_difference, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  have h := field_increment_shift_ball (μ i) (hμ i) (q-referenceCenter i) d
    (nominalError-(actualCenter i-referenceCenter i)) (hr i) (hq i) hd (hn i)
  convert h using 1 <;> congr 2 <;> abel

/-- Per-body mixed-shift envelope compared with charging two separate
absolute field errors using the common gradient gain `2 μ / r³`.
This compares bounds, not all algorithms or actual error magnitudes. -/
theorem shared_shift_envelope_ratio (μ D r N : ℝ) (hr : r ≠ 0) :
    (6*μ/r^4)*D*N = (3*D/(2*r))*((4*μ/r^3)*N) := by
  field_simp
  ring

end GNC.Gravity
