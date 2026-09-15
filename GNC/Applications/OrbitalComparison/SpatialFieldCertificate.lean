import GNC.Applications.OrbitalComparison.SpatialSources
import GNC.Applications.OrbitalComparison.RegionalPrediction
import GNC.Dynamics.InverseRadius

/-! Full-field three-dimensional certificates for computed finite burns.
Both nominal thrust laws and both pointing-offset conventions use this same
checker. All coefficient, radius, source and envelope obligations are checked
independently of the coefficient generator.
-/
namespace GNC.OrbitalComparison.SpatialFieldCertificate
open UniformCertificate WeightedCertificate SpatialBurn SpatialSources Set
open Planning.PolynomialKernel
variable {C : Type} (A : Algebra C)

def cube (u : C) : C := A.base.multiply (A.base.multiply u u) u
def normSq (q : Fin 3 → C) : C :=
  A.base.add (A.base.add (A.base.multiply (q 0) (q 0)) (A.base.multiply (q 1) (q 1)))
    (A.base.multiply (q 2) (q 2))
def normVariation (q : Fin 3 → C) : C := A.base.add (normSq A q) (A.base.scale (-1) A.one)
def inverseVariation (u : C) : C := A.base.add u (A.base.scale (-1) A.one)
def constraint (q : Fin 3 → C) (u : C) : C :=
  A.base.add (A.base.multiply (normSq A q) (A.base.multiply u u)) (A.base.scale (-1) A.one)
def residual (mode : Law) (q : Fin 3 → C) (u : C) (i : Fin 3) : C :=
  A.base.add (A.base.add (A.base.derivative (A.base.derivative (q i)))
    (A.base.scale gravity (A.base.multiply (cube A u) (q i))))
    (A.base.scale (-force) (polynomial A mode i))

def inverseAmplitude (upper b : ℚ) : ℚ := upper*(1+b)
def inverseGain (variation upper b : ℚ) : ℚ :=
  let a := inverseAmplitude upper b
  360000*Direct.gravityParameter/(7000000*(1-variation))^2*(a^2+a+1)/(a+1)

variable (S : TimeRepresentation A.base)

def neededForcing (mode : Law) (q : Fin 3 → C) (u : C) (variation upper b : ℚ) : List ℚ :=
  PolynomialBounds.add
    (PolynomialBounds.scale 7000000 (PolynomialBounds.add
      (PolynomialBounds.add (PolynomialBounds.add (S.envelope (residual A mode q u 0))
        (S.envelope (residual A mode q u 1))) (S.envelope (residual A mode q u 2)))
      [force*sourceError A mode]))
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

def Data.Valid (D : Data (C := C)) (mode : Law) : Prop :=
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
  A.base.bound (A.base.add (A.base.derivative (D.q 1)) (A.base.scale (-omega) A.one)) 0 = 0 ∧
  A.base.bound (A.base.derivative (D.q 2)) 0 = 0 ∧
  PolynomialOrder.prefixes 0 (PolynomialBounds.subtract D.forcing
    (neededForcing A S mode D.q D.inverseRadius D.radiusVariation D.normUpper D.inverseVariationBound)) ∧
  PolynomialEnvelope.Valid D.forcing D.envelope ∧
  evaluate D.envelope 1 ≤ D.positionLimit ∧
  evaluate (differentiate D.envelope) 1/600 ≤ D.velocityLimit

instance (D : Data (C := C)) (mode : Law) : Decidable (D.Valid A S mode) := by
  unfold Data.Valid
  infer_instance

noncomputable section

def position (q : Fin 3 → C) (θ t : ℝ) : E3 :=
  (7000000:ℝ) • pack (A.base.value (q 0) t θ) (A.base.value (q 1) t θ) (A.base.value (q 2) t θ)
def velocity (q : Fin 3 → C) (θ t : ℝ) : E3 :=
  position A (fun i => A.base.derivative (q i)) θ t
def acceleration (q : Fin 3 → C) (θ t : ℝ) : E3 :=
  position A (fun i => A.base.derivative (A.base.derivative (q i))) θ t

theorem position_derivative (q : Fin 3 → C) (θ t : ℝ) :
    HasDerivAt (position A q θ) (velocity A q θ t) t := by
  exact (((A.base.value_derivative (q 0) t θ).smul_const e0).add
    ((A.base.value_derivative (q 1) t θ).smul_const e1) |>.add
    ((A.base.value_derivative (q 2) t θ).smul_const e2)).const_smul (7000000:ℝ)

theorem velocity_derivative (q : Fin 3 → C) (θ t : ℝ) :
    HasDerivAt (velocity A q θ) (acceleration A q θ t) t :=
  position_derivative A (fun i => A.base.derivative (q i)) θ t

theorem normSq_value (q : Fin 3 → C) (θ t : ℝ) :
    A.base.value (normSq A q) t θ =
      (A.base.value (q 0) t θ)^2+(A.base.value (q 1) t θ)^2+(A.base.value (q 2) t θ)^2 := by
  simp only [normSq,A.base.value_add,A.base.value_multiply]
  ring

theorem position_norm_sq (q : Fin 3 → C) (θ t : ℝ) :
    ‖position A q θ t‖^2 = 7000000^2*A.base.value (normSq A q) t θ := by
  rw [position,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,pack_norm_sq,normSq_value]

theorem constraint_value (q : Fin 3 → C) (u : C) (θ t : ℝ) :
    ‖position A q θ t‖^2*(A.base.value u t θ/7000000)^2-1 =
      A.base.value (constraint A q u) t θ := by
  rw [position_norm_sq]
  simp only [constraint,A.base.value_add,A.base.value_multiply,A.base.value_scale,A.value_one,
    Rat.cast_neg,Rat.cast_one]
  ring

theorem bounded_value (p : C) {b : ℚ} (hb : evaluate (S.envelope p) 1 ≤ b)
    {θ t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hθ : |θ| ≤ (angle:ℝ)) :
    |A.base.value p t θ| ≤ (b:ℝ) := by
  have h := (S.sound p ht.1 hθ).trans
    (PolynomialOrder.value_le_endpoint _ (S.nonnegative p) ht)
  have he := PolynomialOrder.value_at_rational (S.envelope p) 1
  rw [Rat.cast_one] at he
  exact h.trans (he.le.trans (by exact_mod_cast hb))

/-- Candidate norm and positive inverse-radius branch are established from
coefficient bounds, before any claim about the physical solution's region. -/
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
  have hq := bounded_value A S _ hqn ht hθ
  have hu := bounded_value A S _ hun ht hθ
  simp only [normVariation,inverseVariation,A.base.value_add,A.base.value_scale,A.value_one,
    Rat.cast_neg,Rat.cast_one,neg_one_mul,← sub_eq_add_neg] at hq hu
  have hn := position_norm_sq A q θ t
  have hbn : (0:ℝ) < b := by exact_mod_cast hb
  have hbl2 : (2:ℝ)*(b:ℝ) < 1 := by
    exact_mod_cast (show 2*b < 1 by linarith)
  have hbl : (b:ℝ) < 1/2 := by linarith
  have hvr : (v:ℝ) < 1 := by exact_mod_cast hv'
  have hupper : (0:ℝ) ≤ upper := by exact_mod_cast hup
  have hupper' : (1:ℝ)+b ≤ (upper:ℝ)^2 := by exact_mod_cast hup'
  have hlo := (abs_le.mp hq).1
  have hhi := (abs_le.mp hq).2
  have hu0 := (abs_le.mp hu).1
  have hu1 := (abs_le.mp hu).2
  have hnorm : 0 ≤ ‖position A q θ t‖ := norm_nonneg _
  have hlower : 7000000*(1-(b:ℝ)) ≤ ‖position A q θ t‖ := by
    nlinarith [sq_nonneg (b:ℝ)]
  have hnormupper : ‖position A q θ t‖ ≤ 7000000*(upper:ℝ) := by nlinarith
  have huposit : 0 ≤ A.base.value u t θ/7000000 := by linarith
  refine ⟨hlower,hnormupper,huposit,?_⟩
  have hmul := mul_le_mul hnormupper
    (show A.base.value u t θ/7000000 ≤ (1+(v:ℝ))/7000000 by linarith)
    huposit (mul_nonneg (by norm_num) hupper)
  convert hmul using 1 <;> simp only [inverseAmplitude,Rat.cast_mul,Rat.cast_add,Rat.cast_one] <;> ring

theorem cube_value (u : C) (θ t : ℝ) : A.base.value (cube A u) t θ = (A.base.value u t θ)^3 := by
  simp only [cube,A.base.value_multiply]
  ring

theorem residual_value (mode : Law) (q : Fin 3 → C) (u : C) (θ t : ℝ) (i : Fin 3) :
    A.base.value (residual A mode q u i) t θ =
      A.base.value (A.base.derivative (A.base.derivative (q i))) t θ+
      (gravity:ℝ)*(A.base.value u t θ)^3*A.base.value (q i) t θ-
      (force:ℝ)*A.base.value (polynomial A mode i) t θ := by
  simp only [residual,A.base.value_add,A.base.value_scale,A.base.value_multiply,
    cube_value,Rat.cast_neg]
  ring

theorem physical_constants :
    (gravity:ℝ) = 360000*mu/7000000^3 ∧
    (force:ℝ) = 360000*(Direct.thrust:ℝ)/7000000 ∧ (0:ℝ) ≤ (Direct.thrust:ℝ) := by
  norm_num [gravity,force,mu,Direct.gravityParameter,Direct.thrust,
    Direct.referenceRadius,Direct.angularSpeed]

def liftedAcceleration (mode : Law) (q : Fin 3 → C) (u : C) (θ t : ℝ) : E3 :=
  (360000:ℝ) • ((-mu*(A.base.value u t θ/7000000)^3) • position A q θ t+
    (Direct.thrust:ℝ) • approximation A mode θ t)

def physicalAcceleration (mode : Law) (θ t : ℝ) (q : E3) : E3 :=
  (360000:ℝ) • (Gravity.field mu q+(Direct.thrust:ℝ) • SpatialBurn.source mode θ t)

theorem residual_identity (mode : Law) (q : Fin 3 → C) (u : C) (θ t : ℝ) :
    acceleration A q θ t-liftedAcceleration A mode q u θ t =
      (7000000:ℝ) • pack (A.base.value (residual A mode q u 0) t θ)
        (A.base.value (residual A mode q u 1) t θ)
        (A.base.value (residual A mode q u 2) t θ) := by
  simp only [residual_value,physical_constants.1,physical_constants.2.1]
  dsimp [acceleration,position,liftedAcceleration,approximation,pack]
  module

theorem inverseGain_value (b upper v : ℚ) : (inverseGain b upper v:ℝ) =
    360000*mu/(7000000*(1-(b:ℝ)))^2*
      Gravity.inverseRadiusFactor (inverseAmplitude upper v:ℝ) := by
  simp only [inverseGain,Gravity.inverseRadiusFactor,Rat.cast_mul,Rat.cast_div,
    Rat.cast_pow,Rat.cast_add,Rat.cast_sub,Rat.cast_ofNat,Rat.cast_one]
  norm_num [Direct.gravityParameter,mu]
  ring

theorem inverseGain_nonnegative {b upper v : ℚ} (hu : 0 ≤ upper) (hv : 0 ≤ v) :
    0 ≤ inverseGain b upper v := by
  unfold inverseGain inverseAmplitude Direct.gravityParameter
  positivity

theorem neededForcing_value (mode : Law) (q : Fin 3 → C) (u : C) (b upper v : ℚ) (t : ℝ) :
    PolynomialOrder.value (neededForcing A S mode q u b upper v) t =
      7000000*(PolynomialOrder.value (S.envelope (residual A mode q u 0)) t+
        PolynomialOrder.value (S.envelope (residual A mode q u 1)) t+
        PolynomialOrder.value (S.envelope (residual A mode q u 2)) t+
        (force:ℝ)*(sourceError A mode:ℝ))+
      (inverseGain b upper v:ℝ)*PolynomialOrder.value (S.envelope (constraint A q u)) t := by
  have hs (a : ℚ) : PolynomialOrder.value [a] t = (a:ℝ) := by
    simp [PolynomialOrder.value,evaluate]
  simp only [neededForcing,PolynomialOrder.value_add,PolynomialOrder.value_scale,hs,
    Rat.cast_mul,Rat.cast_ofNat]

theorem physical_defect (mode : Law) (q : Fin 3 → C) (u : C) {b v upper : ℚ}
    (hb : 0 < b) (hb' : b < 1/2) (hv : 0 ≤ v) (hv' : v < 1)
    (hup : 0 ≤ upper) (hup' : 1+b ≤ upper^2)
    (hqn : evaluate (S.envelope (normVariation A q)) 1 ≤ b)
    (hun : evaluate (S.envelope (inverseVariation A u)) 1 ≤ v)
    {θ t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hθ : |θ| ≤ (angle:ℝ)) :
    ‖acceleration A q θ t-physicalAcceleration mode θ t (position A q θ t)‖ ≤
      PolynomialOrder.value (neededForcing A S mode q u b upper v) t := by
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
      (approximation A mode θ t-SpatialBurn.source mode θ t))‖ ≤
      7000000*(force:ℝ)*(sourceError A mode:ℝ) := by
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ) < 360000),abs_of_nonneg physical_constants.2.2,norm_sub_rev]
    have h := mul_le_mul_of_nonneg_left (approximation_error A mode ht hθ)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 360000) physical_constants.2.2)
    rw [physical_constants.2.1]
    convert h using 1 <;> ring
  have hd : liftedAcceleration A mode q u θ t-physicalAcceleration mode θ t (position A q θ t) =
      (360000:ℝ) • ((-mu*(A.base.value u t θ/7000000)^3) • position A q θ t-
        Gravity.field mu (position A q θ t))+
      (360000:ℝ) • ((Direct.thrust:ℝ) • (approximation A mode θ t-SpatialBurn.source mode θ t)) := by
    dsimp [liftedAcceleration,physicalAcceleration]
    module
  have hxb : ‖acceleration A q θ t-liftedAcceleration A mode q u θ t‖ ≤
      7000000*(PolynomialOrder.value (S.envelope (residual A mode q u 0)) t+
        PolynomialOrder.value (S.envelope (residual A mode q u 1)) t+
        PolynomialOrder.value (S.envelope (residual A mode q u 2)) t) := by
    rw [residual_identity,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 7000000)]
    exact mul_le_mul_of_nonneg_left ((pack_norm_le _ _ _).trans
      (add_le_add (add_le_add (S.sound _ ht.1 hθ) (S.sound _ ht.1 hθ)) (S.sound _ ht.1 hθ)))
      (by norm_num)
  have h := norm_sub_le_norm_sub_add_norm_sub (acceleration A q θ t)
    (liftedAcceleration A mode q u θ t) (physicalAcceleration mode θ t (position A q θ t))
  rw [hd] at h
  have hh := h.trans (add_le_add hxb ((norm_add_le _ _).trans (add_le_add hgb hsb)))
  rw [neededForcing_value]
  convert hh using 1 <;> ring

/-- Physical absolute orbit in normalized time. `v` is 600 times the
inertial velocity in metres per second. Each thrust law has its own nominal. -/
structure PhysicalOrbit (mode : Law) (θ : ℝ) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0 = (7000000:ℝ) • e0
  initial_v : v 0 = (7000000*(omega:ℝ)) • e1
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt v (physicalAcceleration mode θ t (p t)) t

/-- Every checked coefficient record bounds the physical orbit for every
time and every admitted pointing angle, independently of the generator. -/
theorem Data.certifies (D : Data (C := C)) (mode : Law) (hD : D.Valid A S mode)
    {θ : ℝ} (X : PhysicalOrbit mode θ) (hθ : |θ| ≤ (angle:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-position A D.q θ t‖ ≤ (D.positionLimit:ℝ) ∧
      ‖X.v t-velocity A D.q θ t‖/600 ≤ (D.velocityLimit:ℝ) := by
  rcases hD with ⟨hb,hb',hv,hv',hu,hu',hqn,hun,hlip,hfn,hclose,
    hx,hy,hz,hdx,hdy,hdz,hforcing,henv,hpos,hvel⟩
  have hx' := zero_of_bound A.base _ hx hθ
  have hdy' := zero_of_bound A.base _ hdy hθ
  simp only [A.base.value_add,A.base.value_scale,A.value_one,
    Rat.cast_neg,Rat.cast_one,mul_one] at hx' hdy'
  have hxv : A.base.value (D.q 0) 0 θ = 1 := by linarith
  have hdyv : A.base.value (A.base.derivative (D.q 1)) 0 θ = (omega:ℝ) := by linarith
  have hiq : position A D.q θ 0 = (7000000:ℝ) • e0 := by
    simp [position,pack,hxv,zero_of_bound A.base _ hy hθ,zero_of_bound A.base _ hz hθ]
  have hiv : velocity A D.q θ 0 = (7000000*(omega:ℝ)) • e1 := by
    simp [velocity,position,pack,hdyv,zero_of_bound A.base _ hdx hθ,
      zero_of_bound A.base _ hdz hθ,smul_smul]
  have hbt : (2:ℝ)*(D.radiusVariation:ℝ) < 1 := by
    exact_mod_cast (show 2*D.radiusVariation < 1 by linarith)
  have h := orbital_prediction mu 360000 (by norm_num [mu]) (by norm_num)
    X.p X.v (position A D.q θ) (velocity A D.q θ) (acceleration A D.q θ)
    (fun t => (Direct.thrust:ℝ) • SpatialBurn.source mode θ t)
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
      have hd := physical_defect A S mode D.q D.inverseRadius hb hb' hv hv' hu hu' hqn hun ht hθ
      have hf := PolynomialOrder.prefixes_sound _ hforcing ht
      rw [PolynomialOrder.value_subtract] at hf
      rw [norm_sub_rev]
      exact hd.trans (sub_nonneg.mp hf))
  intro t ht
  exact ⟨(h t ht).1.trans (by exact_mod_cast hpos),
    (div_le_div_of_nonneg_right (h t ht).2 (by norm_num)).trans (by exact_mod_cast hvel)⟩

/-- Subtract two certified absolute predictions to bound deviation from
the actual zero-offset nominal for the same prescribed thrust law. -/
theorem Data.relative_certifies (D : Data (C := C)) (mode : Law) (hD : D.Valid A S mode)
    {θ : ℝ} (X : PhysicalOrbit mode θ) (X₀ : PhysicalOrbit mode 0)
    (hθ : |θ| ≤ (angle:ℝ)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖(X.p t-X₀.p t)-(position A D.q θ t-position A D.q 0 t)‖ ≤ 2*(D.positionLimit:ℝ) ∧
      ‖(X.v t-X₀.v t)-(velocity A D.q θ t-velocity A D.q 0 t)‖/600 ≤ 2*(D.velocityLimit:ℝ) := by
  intro t ht
  have h := D.certifies A S mode hD X hθ t ht
  have h₀ := D.certifies A S mode hD X₀ (by norm_num [angle]) t ht
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
end GNC.OrbitalComparison.SpatialFieldCertificate
