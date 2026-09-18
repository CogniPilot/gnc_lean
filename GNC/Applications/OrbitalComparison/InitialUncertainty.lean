import GNC.Applications.OrbitalComparison.VaryingRateTimeCertificate
import GNC.Dynamics.InitialOrbitCertificate
import GNC.Dynamics.InitialOrbitExistence

/-! Initial position and velocity balls for every certified predictor.
A tube is forward containment from the specified initial set; it is not
claimed to be a minimal reachable set or a fixed invariant set. -/
noncomputable section
namespace GNC.OrbitalComparison.InitialUncertainty
open VaryingRateCertificate VaryingRateBurn PointingCapPolynomial SpatialBurn Set
open Planning.PolynomialKernel

structure Motion (D : Data) (θ : ℝ) (p₀ v₀ : ℚ) where
  p : ℝ → E3
  v : ℝ → E3
  continuous_p : Continuous p
  continuous_v : Continuous v
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt v (D.model.acceleration θ t (p t)) t
  initial_p : ‖p 0-D.position θ 0‖≤(p₀:ℝ)
  initial_v : ‖v 0-D.velocity θ 0‖≤(v₀:ℝ)

theorem curve (D : Data) (hD : D.Valid) {p₀ v₀ : ℚ} (f p : List ℚ)
    (hp : InitialPolynomialForcing.Valid D.gain p₀ v₀ f p)
    (hclose : evaluate p 1<D.positionBound)
    {θ : ℝ} (hθ : |θ|≤(D.sigma:ℝ)) (X : Motion D θ p₀ v₀)
    (hdefect : ∀ t ∈ Icc (0:ℝ) 1,
      ‖D.model.acceleration θ t (D.position θ t)-D.acceleration θ t‖≤
        PolynomialOrder.value f t) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖X.p t-D.position θ t‖≤PolynomialOrder.value p t ∧
      ‖X.v t-D.velocity θ t‖≤PolynomialOrder.value (differentiate p) t := by
  have hr : (0:ℝ)<D.r := by exact_mod_cast hD.radius_pos
  have hmax : 2*(D.positionBound:ℝ)<(D.r:ℝ) := by exact_mod_cast hD.position_max
  have hq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (D.r:ℝ)-2*(D.positionBound:ℝ)+(D.positionBound:ℝ)≤‖D.position θ t‖ := by
    have hd := VaryingRatePolynomial.vector_bound D.q hD.position D.kind hθ ht
    have hn := norm_sub_le (D.position θ t) (VaryingRateFrame.turn (D.model.phase t) (D.displacement θ t))
    have he : D.position θ t-VaryingRateFrame.turn (D.model.phase t) (D.displacement θ t)=
        D.model.reference t := by simp [Data.position,VaryingRateFrame.position,Model.reference,Data.model]
    rw [he,D.model.reference_norm hr.le,VaryingRateFrame.turn_norm] at hn
    change ‖D.displacement θ t‖≤(D.positionBound:ℝ) at hd
    change (D.r:ℝ)≤_ at hn
    linarith
  have hM : (0:ℝ)≤D.positionBound := le_trans (norm_nonneg _) <|
    VaryingRatePolynomial.vector_bound D.q hD.position D.kind hθ (show (0:ℝ) ∈ Icc 0 1 by norm_num)
  have hc : PolynomialOrder.value p 1<(D.positionBound:ℝ) := by
    rw [show (1:ℝ)=(1:ℚ) by norm_num,PolynomialOrder.value_at_rational]
    exact_mod_cast hclose
  apply Gravity.initial_polynomial_prediction (D.μ:ℝ) 1
    (by exact_mod_cast hD.mu_nonnegative) (by norm_num)
    X.p X.v (D.position θ) (D.velocity θ) (D.acceleration θ) (D.model.thrust θ)
    f p hp hD.gain_nonnegative hD.gain_max (r := (D.r:ℝ)-2*(D.positionBound:ℝ))
    (by linarith) hM hc (by simp [Data.gain]) hq X.continuous_p X.continuous_v
    (continuous_iff_continuousAt.mpr fun t => (D.position_derivative θ t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (D.velocity_derivative θ t).continuousAt)
    X.derivative_p (fun t ht => by simpa [Model.acceleration] using X.derivative_v t ht)
    (fun t _ => D.position_derivative θ t) (fun t _ => D.velocity_derivative θ t)
    X.initial_p X.initial_v
  intro t ht
  simpa [Model.acceleration] using hdefect t ht

def existenceRadius (D : Data) (p₀ v₀ : ℚ) : ℚ := 4*(D.existenceForce+p₀+v₀)
def existenceFloor (D : Data) (p₀ v₀ : ℚ) : ℚ := D.r-2*existenceRadius D p₀ v₀-(p₀+v₀)

/-- Existence is checked for every point of the initial balls, rather than
merely for their centers. The larger radius is only an existence device. -/
theorem exists_for_initial_offsets (D : Data) (hD : D.Valid) {p₀ v₀ : ℚ}
    (hp₀ : 0≤p₀) (hv₀ : 0≤v₀) (hr : 0<existenceFloor D p₀ v₀)
    (hg : 2*D.μ/(existenceFloor D p₀ v₀)^3≤1)
    {θ : ℝ} (hθ : |θ|≤(D.sigma:ℝ)) (a b : E3)
    (ha : ‖a‖≤(p₀:ℝ)) (hb : ‖b‖≤(v₀:ℝ)) :
    ∃ X : Motion D θ p₀ v₀,
      X.p 0=D.position θ 0+a ∧ X.v 0=D.velocity θ 0+b ∧
      ∀ t ∈ Icc (0:ℝ) 1, (existenceFloor D p₀ v₀:ℝ)≤‖X.p t‖ := by
  have hμ : (0:ℝ)≤D.μ := by exact_mod_cast hD.mu_nonnegative
  have hrD : (0:ℝ)<D.model.r := by
    change (0:ℝ)<(D.r:ℝ)
    exact_mod_cast hD.radius_pos
  have hn : Continuous D.model.nominalThrust := by
    unfold Model.nominalThrust VaryingRateReference.thrust
    dsimp [SpatialRotatingFrame.mix,SpatialBurn.pack,Model.phase,Model.rate]
    fun_prop
  have hgref : Continuous (fun t => Gravity.field D.model.μ (D.model.reference t)) := by
    unfold Gravity.field
    simp only [D.model.reference_norm hrD.le]
    exact continuous_const.smul D.model.reference_continuous
  have hforce (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖D.model.relativeThrust θ t‖≤(D.existenceForce:ℝ) := by
    have h := D.model.relativeThrust_bound θ t hθ (D.force_bound ht)
    simpa only [Data.existenceForce,Rat.cast_mul,Rat.cast_add,Rat.cast_div,
      Rat.cast_pow,Rat.cast_ofNat] using h
  have hR : 0≤existenceRadius D p₀ v₀ := by
    dsimp [existenceRadius]
    positivity [hD.existence_force]
  obtain ⟨p,v,hp,hv,hip,hiv,hdp,hdv,hfloor⟩ := Gravity.exists_near_initial_shift
    hμ (by norm_num : (0:ℝ)≤1)
    (r := (existenceFloor D p₀ v₀:ℝ)) (R := existenceRadius D p₀ v₀)
    (D := (D.existenceForce:ℝ)) (L := ((p₀+v₀:ℚ):ℝ))
    (by exact_mod_cast hr) hR (by exact_mod_cast add_nonneg hp₀ hv₀)
    (by norm_num only [one_mul]; exact_mod_cast hg)
    D.model.reference D.model.referenceVelocity
    (fun t => Gravity.field D.model.μ (D.model.reference t)+D.model.nominalThrust t)
    (D.model.thrust θ) D.model.reference_continuous
    (D.model.referenceVelocity_continuous hrD) (hgref.add hn)
    (hn.add (D.model.relativeThrust_continuous θ))
    (fun t _ => D.model.reference_derivative t)
    (fun t _ => D.model.referenceVelocity_derivative hrD t)
    (by intro t _
        rw [D.model.reference_norm hrD.le]
        simp only [existenceFloor,Data.model,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_ofNat]
        linarith)
    (by exact_mod_cast hD.existence_force)
    (by intro t ht
        convert hforce t ht using 1
        congr 1
        dsimp [Model.thrust,Data.model]
        module)
    (by simp [existenceRadius]; ring_nf; rfl)
    a b (by exact_mod_cast add_le_add ha hb)
  have hi := D.initial hD θ
  have hpref : D.position θ 0=D.model.reference 0 := by
    simp [Data.position,VaryingRateFrame.position,Model.reference,Data.model,hi.1]
  have hvref : D.velocity θ 0=D.model.referenceVelocity 0 := by
    simp [Data.velocity,VaryingRateFrame.velocity,Model.referenceVelocity,Data.model,hi.1,hi.2]
  have hip' : p 0=D.position θ 0+a := by simpa [hpref] using hip
  have hiv' : v 0=D.velocity θ 0+b := by simpa [hvref] using hiv
  refine ⟨⟨p,v,hp,hv,hdp,?_,?_,?_⟩,hip',hiv',hfloor⟩
  · intro t ht
    simpa only [one_smul,Model.acceleration,Data.model] using hdv t ht
  · simpa [hip'] using ha
  · simpa [hiv'] using hb

end GNC.OrbitalComparison.InitialUncertainty
