import GNC.Applications.OrbitalComparison.PointingCapPolynomial
import GNC.Applications.OrbitalComparison.PointingCapDefect
import GNC.Applications.OrbitalComparison.HarmonicCertificate

/-! Certificate data for full physical pointing-cap predictions. Independent
generators may use the same interface; every stored polynomial is checked
against the physical defect, with all omitted gravity and source terms charged. -/
namespace GNC.OrbitalComparison.PointingCapCertificate
open ParameterPolynomial PointingCapPolynomial
open UniformCertificate

structure Data where
  alpha : ℚ
  sigma : ℚ
  radialSource : Option (List ℚ)
  q : PointingCapPolynomial.Vector
  first : PointingCapPolynomial.Vector
  remainder : PointingCapPolynomial.Vector
  witness : PointingCapPolynomial.Vector
  positionBound : ℚ
  firstBound : ℚ
  secondBound : ℚ
  rateBound : ℚ
  residualBound : ℚ

def Data.timeScale (D : Data) : ℚ := 360000*D.alpha^2
def Data.K (D : Data) : ℚ := D.alpha^2*gravity
def Data.W (D : Data) : ℚ := D.alpha*omega
def Data.force (D : Data) : ℚ := D.timeScale*Direct.thrust
def Data.positionOperator (D : Data) (q : PointingCapPolynomial.Vector) : PointingCapPolynomial.Vector :=
  ![scale (2*D.K+D.W^2) (q 0),scale (-D.K+D.W^2) (q 1),scale (-D.K) (q 2)]
def Data.velocityOperator (D : Data) (v : PointingCapPolynomial.Vector) : PointingCapPolynomial.Vector :=
  ![scale (2*D.W) (v 1),scale (-2*D.W) (v 0),[]]
def Data.quadratic (D : Data) : PointingCapPolynomial.Vector :=
  ![add (scale (-3*D.K/7000000) (multiply (D.first 0) (D.first 0)))
       (scale ((3/2)*D.K/7000000)
         (add (multiply (D.first 1) (D.first 1)) (multiply (D.first 2) (D.first 2)))),
    scale (3*D.K/7000000) (multiply (D.first 0) (D.first 1)),
    scale (3*D.K/7000000) (multiply (D.first 0) (D.first 2))]
def Data.source (D : Data) : PointingCapPolynomial.Vector :=
  ![scale (-D.force) (PointingCapPolynomial.source D.radialSource),scale D.force u,scale D.force v]
def Data.rawResidual (D : Data) : PointingCapPolynomial.Vector :=
  difference (difference (difference (difference
    (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.q))
    (D.positionOperator D.q)) (D.velocityOperator (PointingCapPolynomial.derivative D.q)))
    D.source) D.quadratic
def Data.sourceBudget (D : Data) : ℚ := D.force*sourceError D.radialSource D.sigma
def Data.gravityBudget (D : Data) : ℚ := D.timeScale*
  ((3*Direct.gravityParameter/7000000^4)*D.secondBound*(D.positionBound+D.firstBound)+
    (4*Direct.gravityParameter/(7000000-D.positionBound)^5)*D.positionBound^3)
def Data.defect (D : Data) : ℚ := D.residualBound+D.sourceBudget+D.gravityBudget
def Data.gain (D : Data) : ℚ := D.timeScale*2*Direct.gravityParameter/(7000000-2*D.positionBound)^3
def Data.positionError (D : Data) : ℚ := D.defect*HarmonicCertificate.positionGain D.gain
def Data.velocityError (D : Data) : ℚ := D.defect*HarmonicCertificate.velocityGain D.gain/(600*D.alpha)

/-- Each field is an executable finite rational or polynomial check. A data
export constructs this proposition by kernel reduction of those checks. -/
structure Data.Valid (D : Data) : Prop where
  alpha_pos : 0<D.alpha
  alpha_max : D.alpha≤2
  sigma_pos : 0<D.sigma
  sigma_max : D.sigma≤1/10
  initial_p : ∀ i, initialZero (D.q i)
  initial_v : ∀ i, initialZero (ParameterPolynomial.derivative (D.q i))
  source : SourceValid D.radialSource D.sigma
  reduction : ∀ i, zero (subtract (D.rawResidual i)
    (add (D.remainder i) (multiply constraint (D.witness i))))
  position : bounded D.q D.sigma D.positionBound
  first : bounded D.first D.sigma D.firstBound
  second : bounded (difference D.q D.first) D.sigma D.secondBound
  rate : bounded (PointingCapPolynomial.derivative D.q) D.sigma D.rateBound
  residual : bounded D.remainder D.sigma D.residualBound
  position_pos : 0<D.positionBound
  position_max : D.positionBound<3500000
  gain_nonnegative : 0≤D.gain
  gain_max : D.gain<56
  defect_nonnegative : 0≤D.defect
  region : D.positionError<D.positionBound

noncomputable section
open SpatialBurn PointingCapBurn Set

def Data.displacement (D : Data) (x : Fin 3 → ℝ) := vectorValue D.q x
def Data.rotatingVelocity (D : Data) (x : Fin 3 → ℝ) :=
  vectorValue (PointingCapPolynomial.derivative D.q) x
def Data.rotatingAcceleration (D : Data) (x : Fin 3 → ℝ) :=
  vectorValue (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.q)) x
def Data.position (D : Data) (x : Fin 3 → ℝ) := PointingCapFrame.position (D.alpha:ℝ) (D.displacement x)
def Data.velocity (D : Data) (x : Fin 3 → ℝ) :=
  PointingCapFrame.velocity (D.alpha:ℝ) (D.displacement x) (D.rotatingVelocity x)
def Data.acceleration (D : Data) (x : Fin 3 → ℝ) :=
  PointingCapFrame.acceleration (D.alpha:ℝ) (D.displacement x) (D.rotatingVelocity x) (D.rotatingAcceleration x)

theorem Data.valid_sigma (D : Data) (h : D.Valid) : D.sigma^2<1 := by
  nlinarith [h.sigma_pos,h.sigma_max]

theorem Data.positionOperator_value (D : Data) (p : PointingCapPolynomial.Vector) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue (D.positionOperator p) x t=
      PointingCapFrame.positionOperator (D.alpha:ℝ) (vectorValue p x t) := by
  ext i
  fin_cases i <;>
    simp [Data.positionOperator,vectorValue,value_scale,PointingCapFrame.positionOperator,
      HarmonicFrame.positionOperator,HarmonicPolynomial.linear,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,pack_eq,Data.K,Data.W] <;> ring

theorem Data.velocityOperator_value (D : Data) (p : PointingCapPolynomial.Vector) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue (D.velocityOperator p) x t=
      PointingCapFrame.velocityOperator (D.alpha:ℝ) (vectorValue p x t) := by
  ext i
  fin_cases i <;>
    simp [Data.velocityOperator,vectorValue,value_scale,PointingCapFrame.velocityOperator,
      HarmonicFrame.velocityOperator,HarmonicPolynomial.linear,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,pack_eq,Data.W] <;> ring

theorem Data.quadratic_value (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue D.quadratic x t=PointingCapFrame.quadratic (D.alpha:ℝ) (vectorValue D.first x t) := by
  ext i
  fin_cases i <;>
    simp [Data.quadratic,vectorValue,value_scale,value_add,value_multiply,
      PointingCapFrame.quadratic,pack_eq,Data.K] <;> ring

theorem Data.rawResidual_value (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue D.rawResidual x t=PointingCapDefect.residual (D.alpha:ℝ)
      (D.displacement x t) (D.rotatingVelocity x t) (D.rotatingAcceleration x t)
      (vectorValue D.first x t) (vectorValue D.source x t) := by
  simp only [Data.rawResidual,vector_difference,Data.positionOperator_value,
    Data.velocityOperator_value,Data.quadratic_value,PointingCapDefect.residual,
    Data.displacement,Data.rotatingVelocity,Data.rotatingAcceleration]

theorem Data.source_value (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue D.source x t=(D.force:ℝ) •
      pack (-value (PointingCapPolynomial.source D.radialSource) x t) (x 0) (x 1) := by
  ext i
  fin_cases i <;> simp [Data.source,vectorValue,value_scale,pack_eq] <;> ring

theorem Data.force_cast (D : Data) : (D.force:ℝ)=PointingCapFrame.scale (D.alpha:ℝ)*(Direct.thrust:ℝ) := by
  simp [Data.force,Data.timeScale,PointingCapFrame.scale]

theorem Data.source_bound (D : Data) (h : D.Valid) {x : Fin 3 → ℝ}
    (hx : Admissible (D.sigma:ℝ) x) (t : ℝ) :
    ‖vectorValue D.source x t-
      (PointingCapFrame.scale (D.alpha:ℝ)*(Direct.thrust:ℝ)) • (direction x-e0)‖≤(D.sourceBudget:ℝ) := by
  have hf : (0:ℝ)≤D.force := by
    rw [D.force_cast]
    exact mul_nonneg (by unfold PointingCapFrame.scale; positivity)
      SpatialFieldCertificate.physical_constants.2.2
  have he : vectorValue D.source x t-
      (PointingCapFrame.scale (D.alpha:ℝ)*(Direct.thrust:ℝ)) • (direction x-e0) =
      (D.force:ℝ) • ((x 2-value (PointingCapPolynomial.source D.radialSource) x t) • e0) := by
    rw [← D.force_cast,D.source_value]
    dsimp [PointingCapBurn.direction,pack]
    module
  rw [he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hf]
  have hn : ‖e0‖=1 := SpatialExactNominal.plane.norm_x
  rw [hn,mul_one]
  simpa only [Data.sourceBudget,Rat.cast_mul] using
    mul_le_mul_of_nonneg_left (source_error D.radialSource D.sigma h.source hx t) hf

theorem Data.initial (D : Data) (h : D.Valid) (x : Fin 3 → ℝ) :
    D.displacement x 0=0 ∧ D.rotatingVelocity x 0=0 := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [Data.displacement,Data.rotatingVelocity,vectorValue,pack_eq,
      initial_value _ (h.initial_p _),PointingCapPolynomial.derivative,
      initial_value _ (h.initial_v _)]

theorem Data.complete_defect_bound (D : Data) (h : D.Valid) {x : Fin 3 → ℝ}
    (hx : Admissible (D.sigma:ℝ) x) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖PointingCapFrame.physicalAcceleration (D.alpha:ℝ) (direction x) t (D.position x t)-D.acceleration x t‖≤
      (D.defect:ℝ) := by
  have hb (p : PointingCapPolynomial.Vector) (B : ℚ) (hp : bounded p D.sigma B) :=
    vector_bound p h.sigma_pos.le (D.valid_sigma h) hp hx ht
  have hr : vectorValue D.rawResidual x t=vectorValue D.remainder x t := by
    ext i
    fin_cases i <;> simp [vectorValue,pack_eq,reduced_residual _ _ _ (h.reduction _) hx t]
  have hL : ‖PointingCapDefect.residual (D.alpha:ℝ) (D.displacement x t)
      (D.rotatingVelocity x t) (D.rotatingAcceleration x t) (vectorValue D.first x t)
      (vectorValue D.source x t)‖≤(D.residualBound:ℝ) := by
    rw [← D.rawResidual_value,hr]
    exact hb _ _ h.residual
  have hP : (D.positionBound:ℝ)<7000000 :=
    (show (D.positionBound:ℝ)<3500000 by exact_mod_cast h.position_max).trans (by norm_num)
  have hg := PointingCapDefect.physical_defect_bound (D.alpha:ℝ) t (direction x)
    (D.displacement x) (D.rotatingVelocity x) (D.rotatingAcceleration x) (vectorValue D.first x)
    (vectorValue D.source x t) hP (hb _ _ h.position) (hb _ _ h.first)
    (by simpa only [vector_difference] using hb _ _ h.second) hL (D.source_bound h hx t)
  convert hg using 1
  simp [Data.defect,Data.gravityBudget,Data.timeScale,PointingCapFrame.scale,mu,Direct.gravityParameter]

theorem Data.derivative_displacement (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (D.displacement x) (D.rotatingVelocity x t) t := vector_derivative D.q x t
theorem Data.derivative_rotatingVelocity (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (D.rotatingVelocity x) (D.rotatingAcceleration x t) t :=
  vector_derivative (PointingCapPolynomial.derivative D.q) x t
theorem Data.derivative_position (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (D.position x) (D.velocity x t) t :=
  PointingCapFrame.position_derivative _ (D.derivative_displacement x t)
theorem Data.derivative_velocity (D : Data) (x : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (D.velocity x) (D.acceleration x t) t :=
  PointingCapFrame.velocity_derivative _ (D.derivative_displacement x t) (D.derivative_rotatingVelocity x t)

/-- Every accepted record bounds every solution, uniformly over both
transverse pointing directions and over the whole burn. The physical radius
is established by first exit, rather than assumed of an unknown solution. -/
theorem Data.certifies (D : Data) (h : D.Valid) {x : Fin 3 → ℝ}
    (hx : Admissible (D.sigma:ℝ) x) (X : Motion (D.alpha:ℝ) (direction x)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-D.position x t‖≤(D.positionError:ℝ) ∧
      ‖X.v t-D.velocity x t‖/(600*(D.alpha:ℝ))≤(D.velocityError:ℝ) := by
  have ha : (0:ℝ)<D.alpha := by exact_mod_cast h.alpha_pos
  have hs : (D.positionBound:ℝ)<3500000 := by exact_mod_cast h.position_max
  have hclose : (D.defect:ℝ)*PolynomialSupersolution.value (D.gain:ℝ) 1<(D.positionBound:ℝ) := by
    have hh : (D.positionError:ℝ)<(D.positionBound:ℝ) := by exact_mod_cast h.region
    simpa only [Data.positionError,Rat.cast_mul,HarmonicCertificate.positionGain_cast] using hh
  have hq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      7000000-2*(D.positionBound:ℝ)+(D.positionBound:ℝ)≤‖D.position x t‖ := by
    have hb := vector_bound D.q h.sigma_pos.le (D.valid_sigma h) h.position hx ht
    have hn := norm_sub_le (D.position x t) (PointingCapFrame.turn (D.alpha:ℝ) t (D.displacement x t))
    have he : D.position x t-PointingCapFrame.turn (D.alpha:ℝ) t (D.displacement x t)=
        PointingCapFrame.reference (D.alpha:ℝ) t := by simp [Data.position,PointingCapFrame.position]
    rw [he,PointingCapFrame.reference_norm,PointingCapFrame.turn_norm] at hn
    change ‖D.displacement x t‖≤(D.positionBound:ℝ) at hb
    linarith
  have hi := D.initial h x
  have hb := Gravity.constant_prediction mu (PointingCapFrame.scale (D.alpha:ℝ))
    (by norm_num [mu]) (by unfold PointingCapFrame.scale; positivity)
    X.p X.v (D.position x) (D.velocity x) (D.acceleration x)
    (fun t => (Direct.thrust:ℝ) • PointingCapFrame.turn (D.alpha:ℝ) t (direction x))
    (show (0:ℝ)≤D.gain by exact_mod_cast h.gain_nonnegative)
    (show (D.gain:ℝ)<56 by exact_mod_cast h.gain_max)
    (show (0:ℝ)≤D.defect by exact_mod_cast h.defect_nonnegative)
    (r := 7000000-2*(D.positionBound:ℝ)) (by linarith) hclose
    (by simp [Data.gain,Data.timeScale,PointingCapFrame.scale,mu,Direct.gravityParameter]; ring_nf; exact le_rfl)
    hq X.continuous_p X.continuous_v
    (continuous_iff_continuousAt.mpr fun t => (D.derivative_position x t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (D.derivative_velocity x t).continuousAt)
    X.derivative_p X.derivative_v (fun t _ => D.derivative_position x t)
    (fun t _ => D.derivative_velocity x t)
    (by simpa [Data.position,PointingCapFrame.position,hi.1] using X.initial_p)
    (by simpa [Data.velocity,PointingCapFrame.velocity,hi.1,hi.2] using X.initial_v)
    (fun _ ht => D.complete_defect_bound h hx ht)
  intro t ht
  constructor
  · simpa only [Data.positionError,Rat.cast_mul,HarmonicCertificate.positionGain_cast] using (hb t ht).1
  · have hv := div_le_div_of_nonneg_right (hb t ht).2 (by positivity : 0≤600*(D.alpha:ℝ))
    simpa only [Data.velocityError,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,
      HarmonicCertificate.velocityGain_cast] using hv

theorem Data.exists_motion (D : Data) (h : D.Valid) {x : Fin 3 → ℝ}
    (hx : Admissible (D.sigma:ℝ) x) :
    ∃ X : Motion (D.alpha:ℝ) (direction x), ∀ t ∈ Icc (0:ℝ) 1, (6800000:ℝ)≤‖X.p t‖ := by
  apply PointingCapBurn.exists_motion (show (0:ℝ)≤D.alpha by exact_mod_cast h.alpha_pos.le)
    (show (D.alpha:ℝ)≤2 by exact_mod_cast h.alpha_max)
  have hn := direction_bound (show (0:ℝ)≤D.sigma by exact_mod_cast h.sigma_pos.le) hx
  have hs : (D.sigma:ℝ)≤((1/10:ℚ):ℝ) := by exact_mod_cast h.sigma_max
  norm_num at hs
  linarith

def Data.trajectory (D : Data) (h : D.Valid) (x : Fin 3 → ℝ)
    (hx : Admissible (D.sigma:ℝ) x) : Motion (D.alpha:ℝ) (direction x) :=
  Classical.choose (D.exists_motion h hx)

theorem Data.trajectory_unique (D : Data) (h : D.Valid) {x : Fin 3 → ℝ}
    (hx : Admissible (D.sigma:ℝ) x) (X : Motion (D.alpha:ℝ) (direction x)) :
    ∀ t ∈ Icc (0:ℝ) 1, X.p t=(D.trajectory h x hx).p t ∧ X.v t=(D.trajectory h x hx).v t :=
  PointingCapBurn.unique_of_region (show (0:ℝ)≤D.alpha by exact_mod_cast h.alpha_pos.le)
    (show (D.alpha:ℝ)≤2 by exact_mod_cast h.alpha_max) _ X (D.trajectory h x hx)
    (Classical.choose_spec (D.exists_motion h hx))

theorem Data.physical_prediction (D : Data) (h : D.Valid) {x : Fin 3 → ℝ}
    (hx : Admissible (D.sigma:ℝ) x) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖(D.trajectory h x hx).p t-D.position x t‖≤(D.positionError:ℝ) ∧
      ‖(D.trajectory h x hx).v t-D.velocity x t‖/(600*(D.alpha:ℝ))≤(D.velocityError:ℝ) :=
  D.certifies h hx (D.trajectory h x hx)

theorem Data.physical_displacement (D : Data) (h : D.Valid) {x : Fin 3 → ℝ}
    (hx : Admissible (D.sigma:ℝ) x) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(D.trajectory h x hx).p t-PointingCapFrame.reference (D.alpha:ℝ) t‖≤
      ((D.positionBound+D.positionError:ℚ):ℝ) := by
  have hp := (D.physical_prediction h hx t ht).1
  have hd := vector_bound D.q h.sigma_pos.le (D.valid_sigma h) h.position hx ht
  have he : D.position x t-PointingCapFrame.reference (D.alpha:ℝ) t=
      PointingCapFrame.turn (D.alpha:ℝ) t (D.displacement x t) := by
    simp [Data.position,PointingCapFrame.position]
  have hh := norm_sub_le_norm_sub_add_norm_sub ((D.trajectory h x hx).p t)
    (D.position x t) (PointingCapFrame.reference (D.alpha:ℝ) t)
  rw [he,PointingCapFrame.turn_norm] at hh
  change ‖D.displacement x t‖≤(D.positionBound:ℝ) at hd
  push_cast
  linarith

end
end GNC.OrbitalComparison.PointingCapCertificate
