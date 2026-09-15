import GNC.Applications.OrbitalComparison.SpatialFieldCertificate
import GNC.Applications.OrbitalComparison.SpatialRotatingFrame

/-! Full-field certificates retaining the exact reference rotation.
Both finite-angle and ordinary-polynomial candidates use this checker.
The coordinates `q` are absolute positions in the rotating frame divided
by the reference radius. All physical gravity defects are charged.
-/
namespace GNC.OrbitalComparison.SpatialRotatingCertificate
open UniformCertificate WeightedCertificate SpatialBurn SpatialSources Set
open Planning.PolynomialKernel SpatialRotatingFrame
open SpatialFieldCertificate (cube normSq normVariation inverseVariation constraint
  inverseAmplitude inverseGain inverseGain_value inverseGain_nonnegative cube_value physical_constants)
variable {C : Type} (A : Algebra C)

/-- Inertial derivative in rotating components, including the frame rate. -/
def step (q : Fin 3 → C) : Fin 3 → C :=
  ![A.base.add (A.base.derivative (q 0)) (A.base.scale (-omega) (q 1)),
    A.base.add (A.base.derivative (q 1)) (A.base.scale omega (q 0)),
    A.base.derivative (q 2)]

theorem step_value (q : Fin 3 → C) (t θ : ℝ) :
    (fun i => A.base.value (step A q i) t θ) =
      ![A.base.value (A.base.derivative (q 0)) t θ-(omega:ℝ)*A.base.value (q 1) t θ,
        A.base.value (A.base.derivative (q 1)) t θ+(omega:ℝ)*A.base.value (q 0) t θ,
        A.base.value (A.base.derivative (q 2)) t θ] := by
  ext i
  fin_cases i <;> simp [step,A.base.value_add,A.base.value_scale] <;> ring

def residual (q : Fin 3 → C) (u : C) (i : Fin 3) : C :=
  A.base.add (A.base.add (step A (step A q) i)
    (A.base.scale gravity (A.base.multiply (cube A u) (q i))))
    (A.base.scale (-force) (polynomial A .inertiallyFixed i))

/-- Expanding the exact second moving-frame derivative exhibits all
Coriolis and centrifugal terms, with an unchanged normal derivative. -/
theorem step_twice_value (q : Fin 3 → C) (t θ : ℝ) :
    (fun i => A.base.value (step A (step A q) i) t θ) =
      ![A.base.value (A.base.derivative (A.base.derivative (q 0))) t θ-
          2*(omega:ℝ)*A.base.value (A.base.derivative (q 1)) t θ-
          (omega:ℝ)^2*A.base.value (q 0) t θ,
        A.base.value (A.base.derivative (A.base.derivative (q 1))) t θ+
          2*(omega:ℝ)*A.base.value (A.base.derivative (q 0)) t θ-
          (omega:ℝ)^2*A.base.value (q 1) t θ,
        A.base.value (A.base.derivative (A.base.derivative (q 2))) t θ] := by
  have hx : A.base.value (A.base.derivative (step A q 0)) t θ =
      A.base.value (A.base.derivative (A.base.derivative (q 0))) t θ-
        (omega:ℝ)*A.base.value (A.base.derivative (q 1)) t θ := by
    apply (A.base.value_derivative (step A q 0) t θ).unique
    convert (A.base.value_derivative (A.base.derivative (q 0)) t θ).sub
      ((A.base.value_derivative (q 1) t θ).const_mul (omega:ℝ)) using 1
    funext s
    simp [step,A.base.value_add,A.base.value_scale,sub_eq_add_neg]
  have hy : A.base.value (A.base.derivative (step A q 1)) t θ =
      A.base.value (A.base.derivative (A.base.derivative (q 1))) t θ+
        (omega:ℝ)*A.base.value (A.base.derivative (q 0)) t θ := by
    apply (A.base.value_derivative (step A q 1) t θ).unique
    convert (A.base.value_derivative (A.base.derivative (q 1)) t θ).add
      ((A.base.value_derivative (q 0) t θ).const_mul (omega:ℝ)) using 1
    funext s
    simp [step,A.base.value_add,A.base.value_scale]
  rw [step_value]
  ext i
  fin_cases i
  · change A.base.value (A.base.derivative (step A q 0)) t θ-
        (omega:ℝ)*A.base.value (step A q 1) t θ = _
    rw [hx]
    simp [step,A.base.value_add,A.base.value_scale]
    ring
  · change A.base.value (A.base.derivative (step A q 1)) t θ+
        (omega:ℝ)*A.base.value (step A q 0) t θ = _
    rw [hy]
    simp [step,A.base.value_add,A.base.value_scale]
    ring
  · rfl

variable (S : TimeRepresentation A.base)

def neededForcing (q : Fin 3 → C) (u : C) (variation upper b : ℚ) : List ℚ :=
  PolynomialBounds.add
    (PolynomialBounds.scale 7000000 (PolynomialBounds.add
      (PolynomialBounds.add (PolynomialBounds.add (S.envelope (residual A q u 0))
        (S.envelope (residual A q u 1))) (S.envelope (residual A q u 2)))
      [force*sourceError A .inertiallyFixed]))
    (PolynomialBounds.scale (inverseGain variation upper b) (S.envelope (constraint A q u)))

structure Data where
  q : Fin 3 → C
  inverseRadius : C
  radiusVariation : ℚ
  inverseVariationBound : ℚ
  normUpper : ℚ
  forcing : List ℚ
  envelope : List ℚ
  positionLimit : ℚ
  velocityLimit : ℚ

def Data.Valid (D : Data (C := C)) : Prop :=
  0 < D.radiusVariation ∧ D.radiusVariation < 1/2 ∧
  0 ≤ D.inverseVariationBound ∧ D.inverseVariationBound < 1 ∧
  0 ≤ D.normUpper ∧ 1+D.radiusVariation ≤ D.normUpper^2 ∧
  evaluate (S.envelope (normVariation A D.q)) 1 ≤ D.radiusVariation ∧
  evaluate (S.envelope (inverseVariation A D.inverseRadius)) 1 ≤ D.inverseVariationBound ∧
  360000*(2*Direct.gravityParameter/(7000000*(1-2*D.radiusVariation))^3) ≤ 17/20 ∧
  PolynomialOrder.nonnegative D.forcing ∧
  Direct.positionGain*evaluate D.forcing 1 < 7000000*D.radiusVariation ∧
  A.base.bound (A.base.add (D.q 0) (A.base.scale (-1) A.one)) 0 = 0 ∧
  A.base.bound (D.q 1) 0 = 0 ∧ A.base.bound (D.q 2) 0 = 0 ∧
  A.base.bound (A.base.derivative (D.q 0)) 0 = 0 ∧
  A.base.bound (A.base.derivative (D.q 1)) 0 = 0 ∧
  A.base.bound (A.base.derivative (D.q 2)) 0 = 0 ∧
  PolynomialOrder.prefixes 0 (PolynomialBounds.subtract D.forcing
    (neededForcing A S D.q D.inverseRadius D.radiusVariation D.normUpper D.inverseVariationBound)) ∧
  PolynomialEnvelope.Valid D.forcing D.envelope ∧
  evaluate D.envelope 1 ≤ D.positionLimit ∧
  evaluate (differentiate D.envelope) 1/600 ≤ D.velocityLimit

instance (D : Data (C := C)) : Decidable (D.Valid A S) := by
  unfold Data.Valid
  infer_instance

noncomputable section

def position (q : Fin 3 → C) (θ t : ℝ) : E3 :=
  (7000000:ℝ) • mix ((omega:ℝ)*t)
    (A.base.value (q 0) t θ) (A.base.value (q 1) t θ) (A.base.value (q 2) t θ)
def velocity (q : Fin 3 → C) (θ t : ℝ) : E3 := position A (step A q) θ t
def acceleration (q : Fin 3 → C) (θ t : ℝ) : E3 := position A (step A (step A q)) θ t

theorem position_derivative (q : Fin 3 → C) (θ t : ℝ) :
    HasDerivAt (position A q θ) (velocity A q θ t) t := by
  have hφ : HasDerivAt (fun s : ℝ => (omega:ℝ)*s) (omega:ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (omega:ℝ)
  have h := (mix_derivative hφ (A.base.value_derivative (q 0) t θ)
    (A.base.value_derivative (q 1) t θ) (A.base.value_derivative (q 2) t θ)).const_smul (7000000:ℝ)
  convert h using 1
  simp [velocity,position,step,A.base.value_add,A.base.value_scale,sub_eq_add_neg]

theorem velocity_derivative (q : Fin 3 → C) (θ t : ℝ) :
    HasDerivAt (velocity A q θ) (acceleration A q θ t) t :=
  position_derivative A (step A q) θ t

theorem position_norm (q : Fin 3 → C) (θ t : ℝ) :
    ‖position A q θ t‖ = ‖SpatialFieldCertificate.position A q θ t‖ := by
  simp only [position,SpatialFieldCertificate.position,norm_smul,mix_norm]

theorem constraint_value (q : Fin 3 → C) (u : C) (θ t : ℝ) :
    ‖position A q θ t‖^2*(A.base.value u t θ/7000000)^2-1 =
      A.base.value (constraint A q u) t θ := by
  rw [position_norm]
  exact SpatialFieldCertificate.constraint_value A q u θ t

theorem candidate_geometry (q : Fin 3 → C) (u : C) {b v upper : ℚ}
    (hb : 0 < b) (hb' : b < 1/2) (hv : 0 ≤ v) (hv' : v < 1)
    (hup : 0 ≤ upper) (hup' : 1+b ≤ upper^2)
    (hqn : evaluate (S.envelope (normVariation A q)) 1 ≤ b)
    (hun : evaluate (S.envelope (inverseVariation A u)) 1 ≤ v)
    {θ t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hθ : |θ| ≤ (angle:ℝ)) :
    7000000*(1-(b:ℝ)) ≤ ‖position A q θ t‖ ∧
    ‖position A q θ t‖ ≤ 7000000*(upper:ℝ) ∧
    0 ≤ A.base.value u t θ/7000000 ∧
    ‖position A q θ t‖*(A.base.value u t θ/7000000) ≤ (inverseAmplitude upper v:ℝ) := by
  simpa only [position_norm] using
    SpatialFieldCertificate.candidate_geometry A S q u hb hb' hv hv' hup hup' hqn hun ht hθ

def approximation (θ t : ℝ) : E3 :=
  mix ((omega:ℝ)*t) (A.base.value (polynomial A .inertiallyFixed 0) t θ)
    (A.base.value (polynomial A .inertiallyFixed 1) t θ)
    (A.base.value (polynomial A .inertiallyFixed 2) t θ)

theorem approximation_error {θ t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hθ : |θ| ≤ (angle:ℝ)) :
    ‖SpatialBurn.source .rtnReferenceOffset θ t-approximation A θ t‖ ≤
      (sourceError A .inertiallyFixed:ℝ) := by
  rw [rtn_source,approximation,← mix_sub,mix_norm]
  have h := SpatialSources.approximation_error A .inertiallyFixed ht hθ
  convert h using 1
  congr 1
  rw [SpatialBurn.source_components]
  dsimp [SpatialBurn.components,SpatialSources.approximation,pack]
  module

theorem residual_value (q : Fin 3 → C) (u : C) (θ t : ℝ) (i : Fin 3) :
    A.base.value (residual A q u i) t θ =
      A.base.value (step A (step A q) i) t θ+
      (gravity:ℝ)*(A.base.value u t θ)^3*A.base.value (q i) t θ-
      (force:ℝ)*A.base.value (polynomial A .inertiallyFixed i) t θ := by
  simp only [residual,A.base.value_add,A.base.value_scale,A.base.value_multiply,
    cube_value,Rat.cast_neg]
  ring

def liftedAcceleration (q : Fin 3 → C) (u : C) (θ t : ℝ) : E3 :=
  (360000:ℝ) • ((-mu*(A.base.value u t θ/7000000)^3) • position A q θ t+
    (Direct.thrust:ℝ) • approximation A θ t)

theorem residual_identity (q : Fin 3 → C) (u : C) (θ t : ℝ) :
    acceleration A q θ t-liftedAcceleration A q u θ t =
      (7000000:ℝ) • mix ((omega:ℝ)*t) (A.base.value (residual A q u 0) t θ)
        (A.base.value (residual A q u 1) t θ) (A.base.value (residual A q u 2) t θ) := by
  simp only [residual_value,physical_constants.1,physical_constants.2.1]
  dsimp [acceleration,position,liftedAcceleration,approximation,mix,pack]
  module


theorem neededForcing_value (q : Fin 3 → C) (u : C) (b upper v : ℚ) (t : ℝ) :
    PolynomialOrder.value (neededForcing A S q u b upper v) t =
      7000000*(PolynomialOrder.value (S.envelope (residual A q u 0)) t+
        PolynomialOrder.value (S.envelope (residual A q u 1)) t+
        PolynomialOrder.value (S.envelope (residual A q u 2)) t+
        (force:ℝ)*(sourceError A .inertiallyFixed:ℝ))+
      (inverseGain b upper v:ℝ)*PolynomialOrder.value (S.envelope (constraint A q u)) t := by
  have hs (a : ℚ) : PolynomialOrder.value [a] t = (a:ℝ) := by
    simp [PolynomialOrder.value,evaluate]
  simp only [neededForcing,PolynomialOrder.value_add,PolynomialOrder.value_scale,hs,
    Rat.cast_mul,Rat.cast_ofNat]

theorem physical_defect (q : Fin 3 → C) (u : C) {b v upper : ℚ}
    (hb : 0 < b) (hb' : b < 1/2) (hv : 0 ≤ v) (hv' : v < 1)
    (hup : 0 ≤ upper) (hup' : 1+b ≤ upper^2)
    (hqn : evaluate (S.envelope (normVariation A q)) 1 ≤ b)
    (hun : evaluate (S.envelope (inverseVariation A u)) 1 ≤ v)
    {θ t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hθ : |θ| ≤ (angle:ℝ)) :
    ‖acceleration A q θ t-SpatialFieldCertificate.physicalAcceleration .rtnReferenceOffset θ t (position A q θ t)‖ ≤
      PolynomialOrder.value (neededForcing A S q u b upper v) t := by
  obtain ⟨hlow,_hupp,hinv,hamp⟩ := candidate_geometry A S q u hb hb' hv hv' hup hup' hqn hun ht hθ
  have hbl : (b:ℝ) < 1 := by
    have h : (2:ℝ)*(b:ℝ) < 1 := by exact_mod_cast (show 2*b < 1 by linarith)
    linarith
  have hμ : 0 ≤ mu := by norm_num [mu]
  have hg := Gravity.field_inverse_radius_bound mu hμ (position A q θ t)
    (show 0 < 7000000*(1-(b:ℝ)) from mul_pos (by norm_num) (sub_pos.mpr hbl)) hlow hinv hamp
  rw [constraint_value] at hg
  have hgn : (0:ℝ) ≤ (inverseGain b upper v:ℝ) := by
    exact_mod_cast inverseGain_nonnegative (b := b) hup hv
  have hgb : ‖(360000:ℝ) •
      ((-mu*(A.base.value u t θ/7000000)^3) • position A q θ t-
        Gravity.field mu (position A q θ t))‖ ≤
      (inverseGain b upper v:ℝ)*PolynomialOrder.value (S.envelope (constraint A q u)) t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 360000),norm_sub_rev]
    have h := mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 360000)
    have he : 360000*(mu*Gravity.inverseRadiusFactor (inverseAmplitude upper v:ℝ)/
        (7000000*(1-(b:ℝ)))^2*|A.base.value (constraint A q u) t θ|) =
        (inverseGain b upper v:ℝ)*|A.base.value (constraint A q u) t θ| := by
      rw [inverseGain_value]
      ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left (S.sound _ ht.1 hθ) hgn)
  have hsb : ‖(360000:ℝ) • ((Direct.thrust:ℝ) •
      (approximation A θ t-SpatialBurn.source .rtnReferenceOffset θ t))‖ ≤
      7000000*(force:ℝ)*(sourceError A .inertiallyFixed:ℝ) := by
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ) < 360000),abs_of_nonneg physical_constants.2.2,norm_sub_rev]
    have h := mul_le_mul_of_nonneg_left (approximation_error A ht hθ)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 360000) physical_constants.2.2)
    rw [physical_constants.2.1]
    convert h using 1 <;> ring
  have hd : liftedAcceleration A q u θ t-SpatialFieldCertificate.physicalAcceleration .rtnReferenceOffset θ t (position A q θ t) =
      (360000:ℝ) • ((-mu*(A.base.value u t θ/7000000)^3) • position A q θ t-
        Gravity.field mu (position A q θ t))+
      (360000:ℝ) • ((Direct.thrust:ℝ) • (approximation A θ t-SpatialBurn.source .rtnReferenceOffset θ t)) := by
    dsimp [liftedAcceleration,SpatialFieldCertificate.physicalAcceleration]
    module
  have hxb : ‖acceleration A q θ t-liftedAcceleration A q u θ t‖ ≤
      7000000*(PolynomialOrder.value (S.envelope (residual A q u 0)) t+
        PolynomialOrder.value (S.envelope (residual A q u 1)) t+
        PolynomialOrder.value (S.envelope (residual A q u 2)) t) := by
    rw [residual_identity,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 7000000),mix_norm]
    exact mul_le_mul_of_nonneg_left ((pack_norm_le _ _ _).trans
      (add_le_add (add_le_add (S.sound _ ht.1 hθ) (S.sound _ ht.1 hθ)) (S.sound _ ht.1 hθ)))
      (by norm_num)
  have h := norm_sub_le_norm_sub_add_norm_sub (acceleration A q θ t)
    (liftedAcceleration A q u θ t) (SpatialFieldCertificate.physicalAcceleration .rtnReferenceOffset θ t (position A q θ t))
  rw [hd] at h
  have hh := h.trans (add_le_add hxb ((norm_add_le _ _).trans (add_le_add hgb hsb)))
  rw [neededForcing_value]
  convert hh using 1 <;> ring

/-- Every checked coefficient record bounds the physical orbit for every
time and every admitted pointing angle, independently of the generator. -/
theorem Data.certifies (D : Data (C := C)) (hD : D.Valid A S)
    {θ : ℝ} (X : SpatialFieldCertificate.PhysicalOrbit .rtnReferenceOffset θ) (hθ : |θ| ≤ (angle:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-position A D.q θ t‖ ≤ (D.positionLimit:ℝ) ∧
      ‖X.v t-velocity A D.q θ t‖/600 ≤ (D.velocityLimit:ℝ) := by
  rcases hD with ⟨hb,hb',hv,hv',hu,hu',hqn,hun,hlip,hfn,hclose,
    hx,hy,hz,hdx,hdy,hdz,hforcing,henv,hpos,hvel⟩
  have hx' := zero_of_bound A.base _ hx hθ
  simp only [A.base.value_add,A.base.value_scale,A.value_one,
    Rat.cast_neg,Rat.cast_one,mul_one] at hx'
  have hxv : A.base.value (D.q 0) 0 θ = 1 := by linarith
  have hyv := zero_of_bound A.base _ hy hθ
  have hzv := zero_of_bound A.base _ hz hθ
  have hdxv := zero_of_bound A.base _ hdx hθ
  have hdyv := zero_of_bound A.base _ hdy hθ
  have hdzv := zero_of_bound A.base _ hdz hθ
  have hiq : position A D.q θ 0 = (7000000:ℝ) • e0 := by
    simp [position,mix_zero,pack,hxv,hyv,hzv]
  have hiv : velocity A D.q θ 0 = (7000000*(omega:ℝ)) • e1 := by
    simp [velocity,position,step,A.base.value_add,A.base.value_scale,
      hdxv,hdyv,hdzv,hxv,hyv,hzv,mix_zero,pack,smul_smul]
  have hbt : (2:ℝ)*(D.radiusVariation:ℝ) < 1 := by
    exact_mod_cast (show 2*D.radiusVariation < 1 by linarith)
  have h := orbital_prediction mu 360000 (by norm_num [mu]) (by norm_num)
    X.p X.v (position A D.q θ) (velocity A D.q θ) (acceleration A D.q θ)
    (fun t => (Direct.thrust:ℝ) • SpatialBurn.source .rtnReferenceOffset θ t)
    D.forcing D.envelope henv hfn
    (r := 7000000*(1-2*(D.radiusVariation:ℝ))) (M := 7000000*(D.radiusVariation:ℝ))
    (mul_pos (by norm_num) (sub_pos.mpr hbt)) (by
      rw [gain_values.1]
      exact_mod_cast hclose) (by
      have hc : ((360000*(2*Direct.gravityParameter/(7000000*(1-2*D.radiusVariation))^3):ℚ):ℝ) ≤
          ((17/20:ℚ):ℝ) := by exact_mod_cast hlip
      simpa [mu,Direct.gravityParameter] using hc) (by
      intro t ht
      have hg := (candidate_geometry A S D.q D.inverseRadius hb hb' hv hv' hu hu' hqn hun ht hθ).1
      convert hg using 1 <;> ring)
    X.continuous_p X.continuous_v
    (continuous_iff_continuousAt.mpr fun t => (position_derivative A D.q θ t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (velocity_derivative A D.q θ t).continuousAt)
    X.derivative_p X.derivative_v
    (fun t _ => position_derivative A D.q θ t) (fun t _ => velocity_derivative A D.q θ t)
    (X.initial_p.trans hiq.symm) (X.initial_v.trans hiv.symm) (by
      intro t ht
      have hd := physical_defect A S D.q D.inverseRadius hb hb' hv hv' hu hu' hqn hun ht hθ
      have hf := PolynomialOrder.prefixes_sound _ hforcing ht
      rw [PolynomialOrder.value_subtract] at hf
      rw [norm_sub_rev]
      exact hd.trans (sub_nonneg.mp hf))
  intro t ht
  exact ⟨(h t ht).1.trans (by exact_mod_cast hpos),
    (div_le_div_of_nonneg_right (h t ht).2 (by norm_num)).trans (by exact_mod_cast hvel)⟩

/-- Subtract two certified absolute predictions to bound deviation from
the actual zero-offset nominal for the same prescribed thrust law. -/
theorem Data.relative_certifies (D : Data (C := C)) (hD : D.Valid A S)
    {θ : ℝ} (X : SpatialFieldCertificate.PhysicalOrbit .rtnReferenceOffset θ) (X₀ : SpatialFieldCertificate.PhysicalOrbit .rtnReferenceOffset 0)
    (hθ : |θ| ≤ (angle:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖(X.p t-X₀.p t)-(position A D.q θ t-position A D.q 0 t)‖ ≤ 2*(D.positionLimit:ℝ) ∧
      ‖(X.v t-X₀.v t)-(velocity A D.q θ t-velocity A D.q 0 t)‖/600 ≤ 2*(D.velocityLimit:ℝ) := by
  intro t ht
  have h := D.certifies A S hD X hθ t ht
  have h₀ := D.certifies A S hD X₀ (by norm_num [angle]) t ht
  have hp : (X.p t-X₀.p t)-(position A D.q θ t-position A D.q 0 t) =
      (X.p t-position A D.q θ t)-(X₀.p t-position A D.q 0 t) := by abel
  have hv : (X.v t-X₀.v t)-(velocity A D.q θ t-velocity A D.q 0 t) =
      (X.v t-velocity A D.q θ t)-(X₀.v t-velocity A D.q 0 t) := by abel
  rw [hp,hv]
  constructor
  · exact (norm_sub_le _ _).trans (by linarith [h.1,h₀.1])
  · have hh := div_le_div_of_nonneg_right (norm_sub_le (X.v t-velocity A D.q θ t)
      (X₀.v t-velocity A D.q 0 t)) (by norm_num : (0:ℝ) ≤ 600)
    rw [add_div] at hh
    exact hh.trans (by linarith [h.2,h₀.2])

end
end GNC.OrbitalComparison.SpatialRotatingCertificate
