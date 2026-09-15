import GNC.Control.FlatBackstepping

/-! Backstepping through the ideal flat-output, angular-rate, and servo layers.
The aircraft's nonsingular flat and moment allocations are explicit model
conditions. This file proves the complete achieved cascade energy theorem
and the affine moment/servo realization identities.
-/
noncomputable section
namespace GNC.ActuatorBackstepping
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def energy (p v r : E) (β : F) (z s : E) : ℝ :=
  (‖p‖^2+‖v‖^2+‖r‖^2+‖β‖^2+‖z‖^2+‖s‖^2)/2

theorem energy_identity (p v r : E) (β : F) (z s : E)
    (B Bt C Ct : E →L[ℝ] E) (D : E →L[ℝ] F) (Dt : F →L[ℝ] E)
    (kp kv kr kb kz ks : ℝ)
    (hB : inner ℝ r (B z) = inner ℝ z (Bt r))
    (hC : inner ℝ z (C s) = inner ℝ s (Ct z))
    (hD : inner ℝ β (D z) = inner ℝ z (Dt β)) :
    inner ℝ p (-kp • p+v) +
      inner ℝ v (-p-kv • v+r) +
      inner ℝ r (-v-kr • r+B z) +
      inner ℝ β (-kb • β+D z) +
      inner ℝ z (-kz • z-Bt r-Dt β+C s) +
      inner ℝ s (-ks • s-Ct z) =
      -kp*‖p‖^2-kv*‖v‖^2-kr*‖r‖^2-kb*‖β‖^2-kz*‖z‖^2-ks*‖s‖^2 := by
  simp only [inner_add_right, inner_sub_right, inner_neg_right,
    inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v p, real_inner_comm r v, hB, hC, hD]
  ring

/-- Exact trajectory energy decay, including angular-rate and servo errors.
Cross-channel compensation removes the need for a small coupling or a
time-scale separation assumption in this ideal model. -/
theorem exponential_bound {p v r : ℝ → E} {β : ℝ → F} {z s : ℝ → E}
    (B Bt C Ct : ℝ → E →L[ℝ] E)
    (D : ℝ → E →L[ℝ] F) (Dt : ℝ → F →L[ℝ] E)
    {kp kv kr kb kz ks k a b : ℝ}
    (hkp : k ≤ kp) (hkv : k ≤ kv) (hkr : k ≤ kr)
    (hkb : k ≤ kb) (hkz : k ≤ kz) (hks : k ≤ ks)
    (hB : ∀ t x y, inner ℝ x (B t y) = inner ℝ y (Bt t x))
    (hC : ∀ t x y, inner ℝ x (C t y) = inner ℝ y (Ct t x))
    (hD : ∀ t x y, inner ℝ y (D t x) = inner ℝ x (Dt t y))
    (hp : ∀ t, HasDerivAt p (-kp • p t+v t) t)
    (hv : ∀ t, HasDerivAt v (-p t-kv • v t+r t) t)
    (hr : ∀ t, HasDerivAt r (-v t-kr • r t+B t (z t)) t)
    (hb : ∀ t, HasDerivAt β (-kb • β t+D t (z t)) t)
    (hz : ∀ t, HasDerivAt z (-kz • z t-Bt t (r t)-Dt t (β t)+C t (s t)) t)
    (hs : ∀ t, HasDerivAt s (-ks • s t-Ct t (z t)) t) :
    ∀ t ∈ Set.Icc a b, energy (p t) (v t) (r t) (β t) (z t) (s t) ≤
      energy (p a) (v a) (r a) (β a) (z a) (s a)*Real.exp (-2*k*(t-a)) := by
  have hd : ∀ t, HasDerivAt (fun u => energy (p u) (v u) (r u) (β u) (z u) (s u))
      (-kp*‖p t‖^2-kv*‖v t‖^2-kr*‖r t‖^2-kb*‖β t‖^2-kz*‖z t‖^2-ks*‖s t‖^2) t := by
    intro t
    have he := energy_identity (p t) (v t) (r t) (β t) (z t) (s t)
      (B t) (Bt t) (C t) (Ct t) (D t) (Dt t) kp kv kr kb kz ks
      (hB t _ _) (hC t _ _) (hD t _ _)
    convert ((((((hp t).norm_sq.add (hv t).norm_sq).add (hr t).norm_sq).add
      (hb t).norm_sq).add (hz t).norm_sq).add (hs t).norm_sq).div_const 2 using 1
    linarith
  have h := Lyapunov.exponential_bound (c := 2*k) (a := a) (b := b) hd (by
    intro t ht
    dsimp [energy]
    nlinarith [
      mul_nonneg (sub_nonneg.mpr hkp) (sq_nonneg ‖p t‖),
      mul_nonneg (sub_nonneg.mpr hkv) (sq_nonneg ‖v t‖),
      mul_nonneg (sub_nonneg.mpr hkr) (sq_nonneg ‖r t‖),
      mul_nonneg (sub_nonneg.mpr hkb) (sq_nonneg ‖β t‖),
      mul_nonneg (sub_nonneg.mpr hkz) (sq_nonneg ‖z t‖),
      mul_nonneg (sub_nonneg.mpr hks) (sq_nonneg ‖s t‖)])
  simpa only [neg_mul] using h

/-- Moment allocation with a real surface tracking error. The resulting
coupling is exactly I⁻¹G times that error, not an omitted perturbation. -/
theorem moment_allocation (I G : E ≃ₗ[ℝ] E) (drift gyro desired ε : E) :
    I.symm (drift+G (G.symm (I desired+gyro-drift)+ε)-gyro) =
      desired+I.symm (G ε) := by
  simp only [map_add, LinearEquiv.apply_symm_apply]
  have he : drift+(I desired+gyro-drift+G ε)-gyro = I desired+G ε := by abel
  rw [he, map_add, LinearEquiv.symm_apply_apply]

/-- Servo inversion, including the desired-reference derivative and
backstepping correction in the requested derivative. -/
theorem servo_allocation (H : E ≃ₗ[ℝ] E) (drift requested : E) :
  drift+H (H.symm (requested-drift)) = requested := by simp

/-- Lévine's first-order servo equation, with its explicit time-scale factor.
This is an exact inversion for every nonzero epsilon, not a limiting argument. -/
theorem levine_servo_allocation (drift requested : E) {ε : ℝ} (hε : ε ≠ 0) :
    (ε^2)⁻¹ • (drift+((ε^2) • requested-drift)) = requested := by
  rw [← add_sub_assoc, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 hε), one_smul]

/-- The commanded thrust-rate channel is kept while the angular-rate
channel has an error z. The exact output defect is the corresponding three
columns of the flat decoupling map. -/
theorem flat_allocation_with_rate_error (D : (E × F) ≃ₗ[ℝ] (E × F))
    (drift requested : E × F) (z : E) :
    drift+D ((D.symm (requested-drift)).1+z, (D.symm (requested-drift)).2) =
      requested+D (z,0) := by
  have he : ((D.symm (requested-drift)).1+z, (D.symm (requested-drift)).2) =
      D.symm (requested-drift)+(z,0) := by ext <;> simp
  rw [he, map_add, LinearEquiv.apply_symm_apply]
  abel

/-- A realized angular acceleration gives the intended rate-error dynamics
after subtracting the actual derivative of the virtual command. -/
theorem rate_error_derivative {w wc : ℝ → E} {wc' z correction coupling : E}
    {k t : ℝ}
    (hw : HasDerivAt w (wc'-k • z-correction+coupling) t)
    (hc : HasDerivAt wc wc' t) :
    HasDerivAt (fun s => w s-wc s) (-k • z-correction+coupling) t := by
  convert hw.sub hc using 1
  module

theorem surface_error_derivative {surface command : ℝ → E}
    {command' ε correction : E} {k t : ℝ}
    (hs : HasDerivAt surface (command'-k • ε-correction) t)
    (hc : HasDerivAt command command' t) :
    HasDerivAt (fun s => surface s-command s) (-k • ε-correction) t := by
  convert hs.sub hc using 1
  module

/-- Derive every backstepping error equation from the controlled flat-output
kinematics and the realized angular-rate and surface derivatives. In
particular, the derivatives of virtual commands are actual derivatives.
The affine allocation lemmas above supply the corresponding realization
identities. A physical aircraft must still satisfy the stated flat model. -/
theorem physical_error_energy_bound
    {p v a w wc δ δc wc' δc' : ℝ → E} {β : ℝ → F}
    (B Bt C Ct : ℝ → E →L[ℝ] E)
    (D : ℝ → E →L[ℝ] F) (Dt : ℝ → F →L[ℝ] E)
    {kp kv kr kb kz ks k t₀ T : ℝ}
    (hkp : k ≤ kp) (hkv : k ≤ kv) (hkr : k ≤ kr)
    (hkb : k ≤ kb) (hkz : k ≤ kz) (hks : k ≤ ks)
    (hB : ∀ t x y, inner ℝ x (B t y) = inner ℝ y (Bt t x))
    (hC : ∀ t x y, inner ℝ x (C t y) = inner ℝ y (Ct t x))
    (hD : ∀ t x y, inner ℝ y (D t x) = inner ℝ x (Dt t y))
    (hp : ∀ t, HasDerivAt p (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (ha : ∀ t, HasDerivAt a
      (FlatBackstepping.jerk kp kv kr (p t) (v t) (a t)+B t (w t-wc t)) t)
    (hb : ∀ t, HasDerivAt β (-kb • β t+D t (w t-wc t)) t)
    (hwc : ∀ t, HasDerivAt wc (wc' t) t)
    (hδc : ∀ t, HasDerivAt δc (δc' t) t)
    (hw : ∀ t, HasDerivAt w
      (wc' t-kz • (w t-wc t)-
        (Bt t (FlatBackstepping.e₃ kp kv (p t) (v t) (a t))+Dt t (β t))+
        C t (δ t-δc t)) t)
    (hδ : ∀ t, HasDerivAt δ (δc' t-ks • (δ t-δc t)-Ct t (w t-wc t)) t) :
    ∀ t ∈ Set.Icc t₀ T,
      energy (p t) (FlatBackstepping.e₂ kp (p t) (v t))
        (FlatBackstepping.e₃ kp kv (p t) (v t) (a t)) (β t) (w t-wc t) (δ t-δc t) ≤
      energy (p t₀) (FlatBackstepping.e₂ kp (p t₀) (v t₀))
        (FlatBackstepping.e₃ kp kv (p t₀) (v t₀) (a t₀))
        (β t₀) (w t₀-wc t₀) (δ t₀-δc t₀)*Real.exp (-2*k*(t-t₀)) := by
  apply exponential_bound B Bt C Ct D Dt hkp hkv hkr hkb hkz hks hB hC hD
  · intro t
    simpa only [← FlatBackstepping.first_stage] using hp t
  · intro t
    convert FlatBackstepping.e₂_derivative (k₁ := kp) (hp t) (hv t) using 1
    exact (FlatBackstepping.second_stage _ _ _ _ _).symm
  · intro t
    convert FlatBackstepping.e₃_derivative (k₁ := kp) (k₂ := kv)
      (hp t) (hv t) (ha t) using 1
    dsimp [FlatBackstepping.jerk]
    module
  · exact hb
  · intro t
    convert rate_error_derivative (hw t) (hwc t) using 1
    module
  · intro t
    exact surface_error_derivative (hδ t) (hδc t)

end GNC.ActuatorBackstepping
