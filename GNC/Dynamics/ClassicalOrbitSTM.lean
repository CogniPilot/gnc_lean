import GNC.Dynamics.YamanakaAnkersen
import GNC.Dynamics.OrbitalNearAffine
import GNC.Analysis.LinearODE

/-! Classical coast propagation as an exact specialization of the retained
SE₂(3) log-error linear system. The physical nonlinear gravity remainder is
NOT set to zero by this result. YA and HCW solve the retained variational
equations, with explicit frame, phase and endpoint transformations. -/
noncomputable section
open Matrix Real Set
open scoped Matrix.Norms.Operator
namespace GNC.ClassicalOrbitSTM
open ClassicalOrbitEquivalence KeplerAnomaly RadialGravityFrame RotatingVariational

def reorder (F : M6) : YamanakaAnkersen.Block6 :=
  F.submatrix RotatingGravity.originalIndex RotatingGravity.originalIndex

def unreorder (F : YamanakaAnkersen.Block6) : M6 :=
  F.submatrix RotatingGravity.originalIndex.symm RotatingGravity.originalIndex.symm

theorem unreorder_reorder (F : M6) : unreorder (reorder F) = F := by
  ext i j
  simp [unreorder, reorder, Matrix.submatrix]

theorem unreorder_mul (A B : YamanakaAnkersen.Block6) :
    unreorder (A*B) = unreorder A * unreorder B :=
  (Matrix.submatrix_mul_equiv A B RotatingGravity.originalIndex.symm
    RotatingGravity.originalIndex.symm RotatingGravity.originalIndex.symm).symm

theorem reorder_mul (A B : M6) : reorder (A*B) = reorder A * reorder B := by
  exact (Matrix.submatrix_mul_equiv A B RotatingGravity.originalIndex
    RotatingGravity.originalIndex RotatingGravity.originalIndex).symm

theorem reorder_th (k : ℝ) : reorder (th k) = YamanakaAnkersen.generator k :=
  YamanakaAnkersen.th_reindex k

theorem reorder_smul (a : ℝ) (A : M6) : reorder (a • A) = a • reorder A := rfl

theorem reorder_derivative {F : ℝ → M6} {D : M6} {t : ℝ}
    (hF : HasDerivAt F D t) : HasDerivAt (fun s => reorder (F s)) (reorder D) t := by
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hF (RotatingGravity.originalIndex i))
    (RotatingGravity.originalIndex j)

theorem matrix_solution_unique {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (hA : Continuous A)
    (F H : ℝ → Matrix n n ℝ)
    (hF : ∀ t, HasDerivAt F (A t * F t) t)
    (hH : ∀ t, HasDerivAt H (A t * H t) t)
    (s : ℝ) (hs : F s = H s) (t : ℝ) : F t = H t := by
  let L := fun t => ContinuousLinearMap.mul ℝ (Matrix n n ℝ) (A t)
  have hL : Continuous L := (ContinuousLinearMap.mul ℝ (Matrix n n ℝ)).continuous.comp hA
  apply LinearODE.unique_continuous L hL
    (a := -(|s|+|t|+1)) (b := |s|+|t|+1) (t₀ := s)
    (fun u _ => hF u) (fun u _ => hH u) _ hs
  · constructor <;> linarith [le_abs_self t, neg_abs_le t, abs_nonneg s]
  · constructor <;> linarith [le_abs_self s, neg_abs_le s, abs_nonneg t]

def frameChange (e h p : ℝ) (f : ℝ) : M6 :=
  anomalyChange (kappa e f) (kappaPrime e f) (rate e h p f) *
    coordinateChange (omega (rate e h p f))

def frameInverse (e h p : ℝ) (f : ℝ) : M6 :=
  coordinateInverse (omega (rate e h p f)) *
    anomalyInverse (kappa e f) (kappaPrime e f) (rate e h p f)

theorem frame_cancel {e h p : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hh : 0 < h) (hp : 0 < p) (f : ℝ) :
    frameInverse e h p f * frameChange e h p f = 1 := by
  have hc := (anomaly_cancel (kappa_pos he he1 f).ne'
    (rate_pos he he1 hh hp f).ne' (kappaPrime e f)).2
  unfold frameInverse frameChange
  calc
    _ = coordinateInverse (omega (rate e h p f)) *
        (anomalyInverse (kappa e f) (kappaPrime e f) (rate e h p f) *
          anomalyChange (kappa e f) (kappaPrime e f) (rate e h p f)) *
        coordinateChange (omega (rate e h p f)) := by noncomm_ring
    _ = 1 := by rw [hc]; simp

/-- From a physical Kepler clock and a retained log STM to the explicit
YA propagator. This equality includes both endpoint transformations. -/
theorem kepler_stm_equivalence {e h p μ : ℝ}
    (he : 0 ≤ e) (he1 : e < 1) (hh : 0 < h) (hp : 0 < p)
    (hKepler : h^2 = μ*p) (f : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (rate e h p (f t)) t)
    (F : ℝ → M6) (s : ℝ) (hF₀ : F s = 1)
    (hF : ∀ t, HasDerivAt F
      (logGenerator (gravity (μ/(radius e p (f t))^3))
        (omega (rate e h p (f t))) * F t) t) (t : ℝ) :
    reorder (frameChange e h p (f t) * F t) =
      YamanakaAnkersen.transition e (YamanakaAnkersen.secular e (f s)) (f s) (f t) *
        reorder (frameChange e h p (f s)) := by
  let Z := fun t => reorder (frameChange e h p (f t) * F t)
  let P := fun t => YamanakaAnkersen.transition e
    (YamanakaAnkersen.secular e (f s)) (f s) (f t)
  let A := fun t => rate e h p (f t) • YamanakaAnkersen.generator (kappa e (f t))
  have hZ (u : ℝ) : HasDerivAt Z (A u * Z u) u := by
    obtain ⟨_,_,hwd⟩ := coefficient_derivatives hp.ne' (kappa_pos he he1 (f u)).ne' (hf u)
    have hW := omega_derivative hwd
    have hC := to_classical (W := fun t => omega (rate e h p (f t))) hW (hF u)
    have hT := kepler_to_th he he1 hh hp hKepler (hf u) hC
    convert reorder_derivative hT using 1
    · simp only [Z, frameChange, mul_assoc]
    · simp only [A, Z, frameChange, mul_assoc, reorder_mul, reorder_smul, reorder_th]
  have hP (u : ℝ) : HasDerivAt P (A u * P u) u :=
    YamanakaAnkersen.time_transition_derivative he he1 (hf u) s
  have hcF : Continuous f := continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  have hcK : Continuous (fun u => kappa e (f u)) := by unfold kappa; fun_prop
  have hcD : Continuous (fun u => (3:ℝ)/kappa e (f u)) :=
    continuous_const.div hcK (fun u => (kappa_pos he he1 (f u)).ne')
  have hcG : Continuous (fun u => YamanakaAnkersen.generator (kappa e (f u))) := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [YamanakaAnkersen.generator, YamanakaAnkersen.planeGenerator,
        YamanakaAnkersen.normalGenerator] <;> fun_prop
  have hcRate : Continuous (fun u => rate e h p (f u)) := by unfold rate; fun_prop
  have hA : Continuous A := hcRate.smul hcG
  have hH (u : ℝ) : HasDerivAt
      (fun v => P v * reorder (frameChange e h p (f s)))
      (A u * (P u * reorder (frameChange e h p (f s)))) u := by
    simpa only [mul_assoc] using (hP u).mul_const (reorder (frameChange e h p (f s)))
  exact matrix_solution_unique A hA Z _ hZ hH s
    (by simp [Z, P, hF₀, YamanakaAnkersen.transition_initial he he1]) t

/-- Explicit recovery of the log STM from the published YA fundamental
columns. Frame conversion is evaluated at the departure AND arrival epoch. -/
theorem kepler_stm_formula {e h p μ : ℝ}
    (he : 0 ≤ e) (he1 : e < 1) (hh : 0 < h) (hp : 0 < p)
    (hKepler : h^2 = μ*p) (f : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (rate e h p (f t)) t)
    (F : ℝ → M6) (s : ℝ) (hF₀ : F s = 1)
    (hF : ∀ t, HasDerivAt F
      (logGenerator (gravity (μ/(radius e p (f t))^3))
        (omega (rate e h p (f t))) * F t) t) (t : ℝ) :
    F t = frameInverse e h p (f t) *
      unreorder (YamanakaAnkersen.transition e (YamanakaAnkersen.secular e (f s))
        (f s) (f t)) * frameChange e h p (f s) := by
  have H := congrArg unreorder
    (kepler_stm_equivalence he he1 hh hp hKepler f hf F s hF₀ hF t)
  rw [unreorder_reorder, unreorder_mul, unreorder_reorder] at H
  have H' := congrArg (fun Z => frameInverse e h p (f t) * Z) H
  simpa only [← mul_assoc, frame_cancel he he1 hh hp, Matrix.one_mul] using H'

/-- At eccentricity zero, the explicit YA STM is the unique HCW STM after
changing from true-anomaly velocity to physical-time velocity. -/
theorem hcw_ya_equivalence {n : ℝ} (hn : 0 < n)
    (H : ℝ → M6) (hH₀ : H 0 = 1)
    (hH : ∀ t, HasDerivAt H (hcw n * H t) t) (t : ℝ) :
    reorder (anomalyChange 1 0 n * H t) =
      YamanakaAnkersen.transition 0 (YamanakaAnkersen.secular 0 0) 0 (n*t) *
        reorder (anomalyChange 1 0 n) := by
  let C := anomalyChange 1 0 n
  let A := n • YamanakaAnkersen.generator 1
  let P := fun t => YamanakaAnkersen.transition 0 (YamanakaAnkersen.secular 0 0) 0 (n*t)
  have hlink : C * hcw n = (n • th 1) * C := by
    have h := anomaly_connection (k := 1) (w := n) one_ne_zero hn.ne' 0
    have hc := hcw_generator (μ := n^2) (r := 1) (n := n) (by simp)
    simp only [one_pow, div_one] at hc
    simpa [anomalyDerivative, hc, C] using h
  have hZ (u : ℝ) : HasDerivAt (fun t => reorder (C*H t))
      (A * reorder (C*H u)) u := by
    convert reorder_derivative ((hasDerivAt_const u C).mul (hH u)) using 1
    simp only [zero_mul, zero_add, ← mul_assoc, hlink]
    simp only [reorder_mul, reorder_smul, reorder_th, A, mul_assoc]
  have hP (u : ℝ) : HasDerivAt P (A * P u) u := by
    have hf : HasDerivAt (fun t : ℝ => n*t) (rate 0 n 1 (n*u)) u := by
      simpa [rate, kappa] using (hasDerivAt_id u).const_mul n
    simpa [P, A, rate, kappa] using
      YamanakaAnkersen.time_transition_derivative (by norm_num : (0:ℝ) ≤ 0)
        (by norm_num : (0:ℝ) < 1) hf 0
  have hPH (u : ℝ) : HasDerivAt (fun t => P t * reorder C)
      (A * (P u * reorder C)) u := by
    simpa only [mul_assoc] using (hP u).mul_const (reorder C)
  exact matrix_solution_unique (fun _ => A) continuous_const _ _ hZ hPH 0
    (by simp [P, hH₀, YamanakaAnkersen.transition_initial (by norm_num : (0:ℝ) ≤ 0)
      (by norm_num : (0:ℝ) < 1)]) t

def translationProjection (x : LogState) : (Fin 3 ⊕ Fin 3) → ℝ := Sum.elim (x 0) (x 1)

/-- Connect to the paper's actual retained SE₂(3) operator, rather than
merely assigning a matrix with the desired blocks. Thrust is zero here. -/
theorem coast_log_block (μ r n : ℝ) (hr : 0 < r) (R : SO3) (x : LogState) :
    translationProjection (OrbitalNearAffine.linearPart μ R (referencePosition r R)
      ![0,0,![0,0,n]] x) =
      logGenerator (gravity (μ/r^3)) (omega n) *ᵥ translationProjection x := by
  have hg : OrbitalNearAffine.gradient μ R (referencePosition r R) (x 0) =
      gravity (μ/r^3) *ᵥ x 0 := by
    unfold OrbitalNearAffine.gradient
    rw [← Gravity.gradient3_body μ R (referencePosition r R) (x 0)
      (by rw [reference_norm r hr R]; exact hr)]
    exact gradient_diagonal μ r hr R (x 0)
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [translationProjection, OrbitalNearAffine.linearPart, logDrift, ad,
      velocityOnly, hg, logGenerator, gravity, omega, skew, Matrix.mulVec,
      dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ, cross_apply,
      Matrix.cons_val_two, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

end GNC.ClassicalOrbitSTM
