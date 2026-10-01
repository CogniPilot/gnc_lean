import GNC.Preintegration.FohInputError

/-! Certified replacement of a known piecewise-FOH input by a coarser chord.
Node discrepancies bound every interpolated discrepancy. Their uniform
envelopes then give explicit physical R/v/p errors without amplification by
the common gyro rate. This is input-model error, separate from integration. -/
noncomputable section
open Set
namespace GNC.Preintegration.CenteredFoh.InputError.Compression

section Chords
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cancel the shared coarse offset before enclosing the right-endpoint
discrepancy. This identity justifies the native bound evaluator's rearrangement
without treating a subtraction of rounded endpoints as exact. -/
theorem affine_discrepancy_endpoint_rewrite (x y s q : E) (t h : ℝ) :
    (x+h • s)-(y+(t+h) • q) = (x-y-t • q)+h • (s-q) := by
  module

def chord (x y : E) (t : ℝ) : E := (1-t) • x+t • y

/-- Retain separate endpoint discrepancies instead of replacing both by
their maximum. The right side is an affine envelope on the whole hold. -/
theorem chord_error_weights (x₀ x₁ y₀ y₁ : E) {t d₀ d₁ : ℝ}
    (ht : t ∈ Icc 0 1) (h₀ : ‖x₀-y₀‖ ≤ d₀) (h₁ : ‖x₁-y₁‖ ≤ d₁) :
    ‖chord x₀ x₁ t-chord y₀ y₁ t‖ ≤ (1-t)*d₀+t*d₁ := by
  have he : chord x₀ x₁ t-chord y₀ y₁ t =
      (1-t) • (x₀-y₀)+t • (x₁-y₁) := by
    dsimp [chord]
    module
  rw [he]
  calc
    _ ≤ ‖(1-t) • (x₀-y₀)‖+‖t • (x₁-y₁)‖ := norm_add_le _ _
    _ = (1-t)*‖x₀-y₀‖+t*‖x₁-y₁‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left h₁ ht.1)

theorem chord_error (x₀ x₁ y₀ y₁ : E) {t δ : ℝ}
    (ht : t ∈ Icc 0 1) (h₀ : ‖x₀-y₀‖ ≤ δ) (h₁ : ‖x₁-y₁‖ ≤ δ) :
    ‖chord x₀ x₁ t-chord y₀ y₁ t‖ ≤ δ := by
  have he : chord x₀ x₁ t-chord y₀ y₁ t =
      (1-t) • (x₀-y₀)+t • (x₁-y₁) := by
    dsimp [chord]
    module
  rw [he]
  calc
    _ ≤ ‖(1-t) • (x₀-y₀)‖+‖t • (x₁-y₁)‖ := norm_add_le _ _
    _ = (1-t)*‖x₀-y₀‖+t*‖x₁-y₁‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    _ ≤ (1-t)*δ+t*δ := add_le_add
      (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left h₁ ht.1)
    _ = δ := by ring

/-- All intermediate input values are covered, not only the stored knots.
The interval representation is an assumption about the prescribed input,
not about an unknown state or actual intersample sensor motion. -/
theorem piecewise_chord_error (n : ℕ) (x y : Fin (n+1) → E)
    (f g : ℝ → E) {T δ : ℝ}
    (hnode : ∀ i, ‖x i-y i‖ ≤ δ)
    (hpieces : ∀ t ∈ Icc 0 T, ∃ i j : Fin (n+1), ∃ q ∈ Icc (0:ℝ) 1,
      f t = chord (x i) (x j) q ∧ g t = chord (y i) (y j) q) :
    ∀ t ∈ Icc 0 T, ‖f t-g t‖ ≤ δ := by
  intro t ht
  obtain ⟨i,j,q,hq,hf,hg⟩ := hpieces t ht
  rw [hf,hg]
  exact chord_error _ _ _ _ hq (hnode i) (hnode j)

end Chords

/-- Gyro discrepancies use the Euclidean norm, not the default coordinate
supremum norm on `Vec3`. This supplies the affine gyro envelope directly. -/
theorem gyro_chord_error_weights (x₀ x₁ y₀ y₁ : Vec3) {t d₀ d₁ : ℝ}
    (ht : t ∈ Icc 0 1) (h₀ : enorm (x₀-y₀) ≤ d₀) (h₁ : enorm (x₁-y₁) ≤ d₁) :
    enorm ((1-t) • (x₀-y₀)+t • (x₁-y₁)) ≤ (1-t)*d₀+t*d₁ := by
  calc
    _ ≤ enorm ((1-t) • (x₀-y₀))+enorm (t • (x₁-y₁)) := enorm_add_le _ _
    _ = (1-t)*enorm (x₀-y₀)+t*enorm (x₁-y₁) := by
      rw [enorm_smul,enorm_smul,
        abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg ht.1]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left h₁ ht.1)

/-- The physical input-error certificate for affine discrepancy envelopes.
These are exact integrated time weights, with no mean-rate exponential.
Apply on each fine hold, then `composition_error_step` across input jumps. -/
theorem affine_input_error {T dw₀ dw₁ da₀ da₁ abar : ℝ} (hT : 0 < T)
    (R S : ℝ → SO3) (v vh p ph a ah : ℝ → E3) (ω ωh : ℝ → Vec3)
    (hR : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (R s)) (rotation (R t)*hat (ω t)) t)
    (hS : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (S s)) (rotation (S t)*hat (ωh t)) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (rotation (R t) (a t)) t)
    (hvh : ∀ t ∈ Icc 0 T, HasDerivAt vh (rotation (S t) (ah t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hph : ∀ t ∈ Icc 0 T, HasDerivAt ph (vh t) t)
    (hR0 : R 0 = S 0) (hv0 : v 0 = vh 0) (hp0 : p 0 = ph 0)
    (hw : ∀ t ∈ Icc 0 T,
      enorm (ω t-ωh t) ≤ (1-t/T)*dw₀+(t/T)*dw₁)
    (ha : ∀ t ∈ Icc 0 T,
      ‖a t-ah t‖ ≤ (1-t/T)*da₀+(t/T)*da₁)
    (hbar : ∀ t ∈ Icc 0 T, ‖ah t‖ ≤ abar) :
    ‖rotation (R T)-rotation (S T)‖ ≤ T*(dw₀+dw₁)/2 ∧
      ‖v T-vh T‖ ≤ T*(da₀+da₁)/2+abar*T^2*(2*dw₀+dw₁)/6 ∧
      ‖p T-ph T‖ ≤ T^2*(2*da₀+da₁)/6+abar*T^3*(3*dw₀+dw₁)/24 := by
  have h := physical_input_bound R S v vh p ph a ah ω ωh
    (fun t => dw₀*t+(dw₁-dw₀)*t^2/(2*T))
    (fun t => da₀*t+(da₁-da₀)*t^2/(2*T)+
      abar*(dw₀*t^2/2+(dw₁-dw₀)*t^3/(6*T)))
    (fun t => da₀*t^2/2+(da₁-da₀)*t^3/(6*T)+
      abar*(dw₀*t^3/6+(dw₁-dw₀)*t^4/(24*T)))
    (fun t => (1-t/T)*dw₀+(t/T)*dw₁)
    (fun t => (1-t/T)*da₀+(t/T)*da₁)
    hR hS hv hvh hp hph hR0 hv0 hp0
    (by simp) (by simp) (by simp)
    (fun t => by
      convert ((hasDerivAt_id t).const_mul dw₀).add
        (((hasDerivAt_pow 2 t).const_mul (dw₁-dw₀)).div_const (2*T)) using 1 <;> ring)
    (fun t => by
      convert (((hasDerivAt_id t).const_mul da₀).add
        (((hasDerivAt_pow 2 t).const_mul (da₁-da₀)).div_const (2*T))).add
        (((((hasDerivAt_pow 2 t).const_mul dw₀).div_const 2).add
          (((hasDerivAt_pow 3 t).const_mul (dw₁-dw₀)).div_const (6*T))).const_mul abar)
        using 1 <;> ring)
    (fun t => by
      convert ((((hasDerivAt_pow 2 t).const_mul da₀).div_const 2).add
        (((hasDerivAt_pow 3 t).const_mul (da₁-da₀)).div_const (6*T))).add
        (((((hasDerivAt_pow 3 t).const_mul dw₀).div_const 6).add
          (((hasDerivAt_pow 4 t).const_mul (dw₁-dw₀)).div_const (24*T))).const_mul abar)
        using 1 <;> ring)
    hw ha hbar
  obtain ⟨hr,hv,hp⟩ := h T ⟨hT.le,le_rfl⟩
  refine ⟨?_,?_,?_⟩
  · convert hr using 1
    field_simp [ne_of_gt hT]
    ring
  · convert hv using 1
    field_simp [ne_of_gt hT]
    ring
  · convert hp using 1
    field_simp [ne_of_gt hT]
    ring

/-- Retaining endpoint time weights cannot worsen the corresponding
uniform local budget. Equal endpoints recover it exactly. -/
theorem affine_budget_le_uniform {T dw₀ dw₁ da₀ da₁ dw da abar : ℝ}
    (hT : 0 ≤ T) (hbar : 0 ≤ abar)
    (hw₀ : dw₀ ≤ dw) (hw₁ : dw₁ ≤ dw)
    (ha₀ : da₀ ≤ da) (ha₁ : da₁ ≤ da) :
    T*(dw₀+dw₁)/2 ≤ dw*T ∧
      T*(da₀+da₁)/2+abar*T^2*(2*dw₀+dw₁)/6 ≤ da*T+abar*dw*T^2/2 ∧
      T^2*(2*da₀+da₁)/6+abar*T^3*(3*dw₀+dw₁)/24 ≤
        da*T^2/2+abar*dw*T^3/6 := by
  have hw : (dw₀+dw₁)/2 ≤ dw := by linarith
  have hvw : (2*dw₀+dw₁)/6 ≤ dw/2 := by linarith
  have hpw : (3*dw₀+dw₁)/24 ≤ dw/6 := by linarith
  have hva : (da₀+da₁)/2 ≤ da := by linarith
  have hpa : (2*da₀+da₁)/6 ≤ da/2 := by linarith
  refine ⟨?_,?_,?_⟩
  · convert mul_le_mul_of_nonneg_left hw hT using 1 <;> ring
  · convert add_le_add (mul_le_mul_of_nonneg_left hva hT)
      (mul_le_mul_of_nonneg_left hvw (mul_nonneg hbar (sq_nonneg T))) using 1 <;> ring
  · convert add_le_add (mul_le_mul_of_nonneg_left hpa (sq_nonneg T))
      (mul_le_mul_of_nonneg_left hpw (mul_nonneg hbar (pow_nonneg hT 3))) using 1 <;> ring

/-- An explicit hold-replacement budget. The knot theorem supplies the
input discrepancy envelopes for a prescribed piecewise-affine input. -/
theorem uniform_input_error {T dw da abar : ℝ} (hT : 0 ≤ T)
    (R S : ℝ → SO3) (v vh p ph a ah : ℝ → E3) (ω ωh : ℝ → Vec3)
    (hR : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (R s)) (rotation (R t)*hat (ω t)) t)
    (hS : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => rotation (S s)) (rotation (S t)*hat (ωh t)) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (rotation (R t) (a t)) t)
    (hvh : ∀ t ∈ Icc 0 T, HasDerivAt vh (rotation (S t) (ah t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hph : ∀ t ∈ Icc 0 T, HasDerivAt ph (vh t) t)
    (hR0 : R 0 = S 0) (hv0 : v 0 = vh 0) (hp0 : p 0 = ph 0)
    (hw : ∀ t ∈ Icc 0 T, enorm (ω t-ωh t) ≤ dw)
    (ha : ∀ t ∈ Icc 0 T, ‖a t-ah t‖ ≤ da)
    (hbar : ∀ t ∈ Icc 0 T, ‖ah t‖ ≤ abar) :
    ‖rotation (R T)-rotation (S T)‖ ≤ dw*T ∧
      ‖v T-vh T‖ ≤ da*T+abar*dw*T^2/2 ∧
      ‖p T-ph T‖ ≤ da*T^2/2+abar*dw*T^3/6 := by
  have h := physical_input_bound R S v vh p ph a ah ω ωh
    (fun t => dw*t) (fun t => da*t+abar*dw*t^2/2)
    (fun t => da*t^2/2+abar*dw*t^3/6)
    (fun _ => dw) (fun _ => da)
    hR hS hv hvh hp hph hR0 hv0 hp0
    (by ring) (by ring) (by ring)
    (fun t => by simpa using (hasDerivAt_id t).const_mul dw)
    (fun t => by
      convert ((hasDerivAt_id t).const_mul da).add
        (((hasDerivAt_pow 2 t).const_mul (abar*dw)).div_const 2) using 1
      ring)
    (fun t => by
      convert (((hasDerivAt_pow 2 t).const_mul da).div_const 2).add
        (((hasDerivAt_pow 3 t).const_mul (abar*dw)).div_const 6) using 1
      ring)
    hw ha hbar
  exact h T ⟨hT,le_rfl⟩

/-- Bounds on the coarse increment used by physical composition, derived
from its ODE rather than assumed of the unknown coarse solution. -/
theorem reference_increment_bound {T abar : ℝ} (hT : 0 ≤ T)
    (S : ℝ → SO3) (v p a : ℝ → E3)
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (rotation (S t) (a t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hv0 : v 0 = 0) (hp0 : p 0 = 0)
    (ha : ∀ t ∈ Icc 0 T, ‖a t‖ ≤ abar) :
    ‖v T‖ ≤ abar*T ∧ ‖p T‖ ≤ abar*T^2/2 := by
  have h1 := norm_le_primitive v (fun t => rotation (S t) (a t))
    (fun t => abar*t) (fun _ => abar) hv
    (fun t => by simpa using (hasDerivAt_id t).const_mul abar)
    hv0 (by ring) (fun t ht => by simpa only [rotation_norm_apply] using ha t ht)
  have h2 := norm_le_primitive p v (fun t => abar*t^2/2) (fun t => abar*t) hp
    (fun t => by
      convert ((hasDerivAt_pow 2 t).const_mul abar).div_const 2 using 1
      ring)
    hp0 (by ring) h1
  exact ⟨h1 T ⟨hT,le_rfl⟩,h2 T ⟨hT,le_rfl⟩⟩

/-- The operator representation preserves the actual SO(3) product. -/
theorem rotation_composition (R Q : SO3) :
    rotation (R*Q) = rotation R*rotation Q := by
  change matrixOp (R.val*Q.val) = matrixOp R.val*matrixOp Q.val
  exact map_mul matrixOp R.val Q.val

/-- Composition retains the clock-to-position term and true rotation
isometry. This permits finitely many FOH pieces without requiring an ODE
derivative at an input jump between them. -/
theorem composition_error_step (R S Q H : SO3) (v vh p ph vl vhl pl phl : E3)
    {h r ev ep br bv bp av ap : ℝ} (hh : 0 ≤ h)
    (hr : ‖rotation R-rotation S‖ ≤ r) (hev : ‖v-vh‖ ≤ ev)
    (hep : ‖p-ph‖ ≤ ep) (hbr : ‖rotation Q-rotation H‖ ≤ br)
    (hbv : ‖vl-vhl‖ ≤ bv) (hbp : ‖pl-phl‖ ≤ bp)
    (hav : ‖vhl‖ ≤ av) (hap : ‖phl‖ ≤ ap) :
    ‖rotation R*rotation Q-rotation S*rotation H‖ ≤ r+br ∧
      ‖(v+rotation R vl)-(vh+rotation S vhl)‖ ≤ ev+bv+av*r ∧
      ‖(p+h • v+rotation R pl)-(ph+h • vh+rotation S phl)‖ ≤
        ep+h*ev+bp+ap*r := by
  have hrnew : ‖rotation R*rotation Q-rotation S*rotation H‖ ≤ r+br := by
    have he : rotation R*rotation Q-rotation S*rotation H =
        rotation R*(rotation Q-rotation H)+(rotation R-rotation S)*rotation H := by
      rw [mul_sub,sub_mul]
      abel
    rw [he]
    calc
      _ ≤ ‖rotation R*(rotation Q-rotation H)‖+
          ‖(rotation R-rotation S)*rotation H‖ := norm_add_le _ _
      _ ≤ ‖rotation R‖*‖rotation Q-rotation H‖+
          ‖rotation R-rotation S‖*‖rotation H‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = ‖rotation Q-rotation H‖+‖rotation R-rotation S‖ := by
        rw [rotation_norm,rotation_norm]
        ring
      _ ≤ r+br := by linarith
  have hvlocal := velocity_input_rate R S vl vhl hbv hr hav
  have hplocal := velocity_input_rate R S pl phl hbp hr hap
  have hvnew : ‖(v+rotation R vl)-(vh+rotation S vhl)‖ ≤ ev+bv+av*r := by
    have he : (v+rotation R vl)-(vh+rotation S vhl) =
        (v-vh)+(rotation R vl-rotation S vhl) := by abel
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add hev hvlocal).trans_eq (by ring))
  have hpnew : ‖(p+h • v+rotation R pl)-(ph+h • vh+rotation S phl)‖ ≤
      ep+h*ev+bp+ap*r := by
    have he : (p+h • v+rotation R pl)-(ph+h • vh+rotation S phl) =
        (p-ph)+h • (v-vh)+(rotation R pl-rotation S phl) := by
      rw [smul_sub]
      abel
    rw [he]
    have hvel : ‖h • (v-vh)‖ ≤ h*ev := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left hev hh
    exact ((norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)).trans
      ((add_le_add (add_le_add hep hvel) hplocal).trans_eq (by ring))
  exact ⟨hrnew,hvnew,hpnew⟩

/-- The scalar physical-composition recurrence is monotone in every error
budget. Together with the local affine comparison this permits repeated
improvements without reintroducing the uniform maximum. -/
theorem budget_step_mono {h av ap r ev ep br bv bp R V P BR BV BP : ℝ}
    (hh : 0 ≤ h) (hav : 0 ≤ av) (hap : 0 ≤ ap)
    (hr : r ≤ R) (hev : ev ≤ V) (hep : ep ≤ P)
    (hbr : br ≤ BR) (hbv : bv ≤ BV) (hbp : bp ≤ BP) :
    r+br ≤ R+BR ∧
      ev+bv+av*r ≤ V+BV+av*R ∧
      ep+h*ev+bp+ap*r ≤ P+h*V+BP+ap*R := by
  refine ⟨add_le_add hr hbr,?_,?_⟩
  · exact add_le_add (add_le_add hev hbv) (mul_le_mul_of_nonneg_left hr hav)
  · exact add_le_add
      (add_le_add (add_le_add hep (mul_le_mul_of_nonneg_left hev hh)) hbp)
      (mul_le_mul_of_nonneg_left hr hap)

/-- The uniform hold-replacement budget is preserved under the physical
composition recurrence. These are algebraic identities, not fitted margins. -/
theorem uniform_budget_step (dw da abar t h : ℝ) :
    dw*t+dw*h = dw*(t+h) ∧
    (da*t+abar*dw*t^2/2)+(da*h+abar*dw*h^2/2)+(abar*h)*(dw*t) =
      da*(t+h)+abar*dw*(t+h)^2/2 ∧
    (da*t^2/2+abar*dw*t^3/6)+h*(da*t+abar*dw*t^2/2)+
      (da*h^2/2+abar*dw*h^3/6)+(abar*h^2/2)*(dw*t) =
      da*(t+h)^2/2+abar*dw*(t+h)^3/6 := by
  constructor
  · ring
  constructor <;> ring

end GNC.Preintegration.CenteredFoh.InputError.Compression
