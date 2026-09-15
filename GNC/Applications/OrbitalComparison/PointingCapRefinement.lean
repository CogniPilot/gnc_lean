import GNC.Applications.OrbitalComparison.PointingCapCertificate

/-! Replace the coefficient-box estimates of a checked predictor by any proved
uniform norm estimates. This interface reuses the same coefficients, source
certificate, physical ODE and existence proof. A new range algorithm must
prove `Sound`; numerical proposals alone do not satisfy the interface. -/
namespace GNC.OrbitalComparison.PointingCapRefinement
open PointingCapCertificate PointingCapPolynomial PointingCapBurn
open SpatialBurn Set

structure Bounds where
  position : ℚ
  first : ℚ
  second : ℚ
  remainder : ℚ

def coefficientBounds (D : Data) : Bounds :=
  ⟨D.positionBound,D.firstBound,D.secondBound,D.residualBound⟩

def Bounds.minimum (B C : Bounds) : Bounds :=
  ⟨min B.position C.position,min B.first C.first,
    min B.second C.second,min B.remainder C.remainder⟩

def Bounds.defect (B : Bounds) (D : Data) : ℚ :=
  B.remainder+D.sourceBudget+D.timeScale*
    ((3*Direct.gravityParameter/7000000^4)*B.second*(B.position+B.first)+
      (4*Direct.gravityParameter/(7000000-B.position)^5)*B.position^3)
def Bounds.gain (B : Bounds) (D : Data) : ℚ :=
  D.timeScale*2*Direct.gravityParameter/(7000000-2*B.position)^3
def Bounds.positionError (B : Bounds) (D : Data) : ℚ :=
  B.defect D*HarmonicCertificate.positionGain (B.gain D)
def Bounds.velocityError (B : Bounds) (D : Data) : ℚ :=
  B.defect D*HarmonicCertificate.velocityGain (B.gain D)/(600*D.alpha)

structure Bounds.Checks (B : Bounds) (D : Data) : Prop where
  position_pos : 0<B.position
  position_max : B.position<3500000
  gain_nonnegative : 0≤B.gain D
  gain_max : B.gain D<56
  defect_nonnegative : 0≤B.defect D
  region : B.positionError D<B.position

noncomputable section

structure Bounds.Sound (B : Bounds) (D : Data) : Prop where
  position : ∀ x, Admissible (D.sigma:ℝ) x → ∀ t ∈ Icc (0:ℝ) 1,
    ‖D.displacement x t‖≤(B.position:ℝ)
  first : ∀ x, Admissible (D.sigma:ℝ) x → ∀ t ∈ Icc (0:ℝ) 1,
    ‖vectorValue D.first x t‖≤(B.first:ℝ)
  second : ∀ x, Admissible (D.sigma:ℝ) x → ∀ t ∈ Icc (0:ℝ) 1,
    ‖D.displacement x t-vectorValue D.first x t‖≤(B.second:ℝ)
  remainder : ∀ x, Admissible (D.sigma:ℝ) x → ∀ t ∈ Icc (0:ℝ) 1,
    ‖vectorValue D.remainder x t‖≤(B.remainder:ℝ)

theorem coefficientBounds_sound (D : Data) (hD : D.Valid) : (coefficientBounds D).Sound D := by
  have h (p : PointingCapPolynomial.Vector) (b : ℚ) (hb : bounded p D.sigma b)
      (x : Fin 3 → ℝ) (hx : Admissible (D.sigma:ℝ) x) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :=
    vector_bound p hD.sigma_pos.le (D.valid_sigma hD) hb hx ht
  refine ⟨h _ _ hD.position,h _ _ hD.first,?_,h _ _ hD.residual⟩
  intro x hx t ht
  simpa only [vector_difference] using h _ _ hD.second x hx t ht

/-- Independently proved range estimates can be combined componentwise.
The scalar region and supersolution checks must still be established. -/
theorem Bounds.minimum_sound (B C : Bounds) (D : Data) (hB : B.Sound D) (hC : C.Sound D) :
    (B.minimum C).Sound D := by
  constructor
  · intro x hx t ht
    simpa only [minimum,Rat.cast_min] using le_min (hB.position x hx t ht) (hC.position x hx t ht)
  · intro x hx t ht
    simpa only [minimum,Rat.cast_min] using le_min (hB.first x hx t ht) (hC.first x hx t ht)
  · intro x hx t ht
    simpa only [minimum,Rat.cast_min] using le_min (hB.second x hx t ht) (hC.second x hx t ht)
  · intro x hx t ht
    simpa only [minimum,Rat.cast_min] using le_min (hB.remainder x hx t ht) (hC.remainder x hx t ht)

theorem Bounds.complete_defect (B : Bounds) (D : Data) (hD : D.Valid)
    (hB : B.Sound D) (hC : B.Checks D) {x : Fin 3 → ℝ}
    (hx : Admissible (D.sigma:ℝ) x) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖PointingCapFrame.physicalAcceleration (D.alpha:ℝ) (direction x) t (D.position x t)-
      D.acceleration x t‖≤(B.defect D:ℝ) := by
  have hr : vectorValue D.rawResidual x t=vectorValue D.remainder x t := by
    ext i
    fin_cases i <;> simp [vectorValue,pack_eq,reduced_residual _ _ _ (hD.reduction _) hx t]
  have hL : ‖PointingCapDefect.residual (D.alpha:ℝ) (D.displacement x t)
      (D.rotatingVelocity x t) (D.rotatingAcceleration x t) (vectorValue D.first x t)
      (vectorValue D.source x t)‖≤(B.remainder:ℝ) := by
    rw [← D.rawResidual_value,hr]
    exact hB.remainder x hx t ht
  have hP : (B.position:ℝ)<7000000 :=
    (show (B.position:ℝ)<3500000 by exact_mod_cast hC.position_max).trans (by norm_num)
  have h := PointingCapDefect.physical_defect_bound (D.alpha:ℝ) t (direction x)
    (D.displacement x) (D.rotatingVelocity x) (D.rotatingAcceleration x) (vectorValue D.first x)
    (vectorValue D.source x t) hP (hB.position x hx t ht) (hB.first x hx t ht)
    (hB.second x hx t ht) hL (D.source_bound hD hx t)
  convert h using 1
  simp [Bounds.defect,Data.timeScale,PointingCapFrame.scale,mu,Direct.gravityParameter]

/-- New norm estimates give new physical error bounds for every solution.
Neither a new numerical trajectory nor a new gravity model is introduced. -/
theorem Bounds.certifies (B : Bounds) (D : Data) (hD : D.Valid)
    (hB : B.Sound D) (hC : B.Checks D) {x : Fin 3 → ℝ}
    (hx : Admissible (D.sigma:ℝ) x) (X : Motion (D.alpha:ℝ) (direction x)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-D.position x t‖≤(B.positionError D:ℝ) ∧
      ‖X.v t-D.velocity x t‖/(600*(D.alpha:ℝ))≤(B.velocityError D:ℝ) := by
  have ha : (0:ℝ)<D.alpha := by exact_mod_cast hD.alpha_pos
  have hs : (B.position:ℝ)<3500000 := by exact_mod_cast hC.position_max
  have hclose : (B.defect D:ℝ)*PolynomialSupersolution.value (B.gain D:ℝ) 1<(B.position:ℝ) := by
    have hh : (B.positionError D:ℝ)<(B.position:ℝ) := by exact_mod_cast hC.region
    simpa only [Bounds.positionError,Rat.cast_mul,HarmonicCertificate.positionGain_cast] using hh
  have hq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      7000000-2*(B.position:ℝ)+(B.position:ℝ)≤‖D.position x t‖ := by
    have hb := hB.position x hx t ht
    have hn := norm_sub_le (D.position x t) (PointingCapFrame.turn (D.alpha:ℝ) t (D.displacement x t))
    have he : D.position x t-PointingCapFrame.turn (D.alpha:ℝ) t (D.displacement x t)=
        PointingCapFrame.reference (D.alpha:ℝ) t := by simp [Data.position,PointingCapFrame.position]
    rw [he,PointingCapFrame.reference_norm,PointingCapFrame.turn_norm] at hn
    linarith
  have hi := D.initial hD x
  have h := Gravity.constant_prediction mu (PointingCapFrame.scale (D.alpha:ℝ))
    (by norm_num [mu]) (by unfold PointingCapFrame.scale; positivity)
    X.p X.v (D.position x) (D.velocity x) (D.acceleration x)
    (fun t => (Direct.thrust:ℝ) • PointingCapFrame.turn (D.alpha:ℝ) t (direction x))
    (show (0:ℝ)≤B.gain D by exact_mod_cast hC.gain_nonnegative)
    (show (B.gain D:ℝ)<56 by exact_mod_cast hC.gain_max)
    (show (0:ℝ)≤B.defect D by exact_mod_cast hC.defect_nonnegative)
    (r := 7000000-2*(B.position:ℝ)) (by linarith) hclose
    (by simp [Bounds.gain,Data.timeScale,PointingCapFrame.scale,mu,Direct.gravityParameter]; ring_nf; exact le_rfl)
    hq X.continuous_p X.continuous_v
    (continuous_iff_continuousAt.mpr fun t => (D.derivative_position x t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (D.derivative_velocity x t).continuousAt)
    X.derivative_p X.derivative_v (fun t _ => D.derivative_position x t)
    (fun t _ => D.derivative_velocity x t)
    (by simpa [Data.position,PointingCapFrame.position,hi.1] using X.initial_p)
    (by simpa [Data.velocity,PointingCapFrame.velocity,hi.1,hi.2] using X.initial_v)
    (fun _ ht => B.complete_defect D hD hB hC hx ht)
  intro t ht
  constructor
  · simpa only [Bounds.positionError,Rat.cast_mul,HarmonicCertificate.positionGain_cast] using (h t ht).1
  · have hv := div_le_div_of_nonneg_right (h t ht).2 (by positivity : 0≤600*(D.alpha:ℝ))
    simpa only [Bounds.velocityError,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,
      HarmonicCertificate.velocityGain_cast] using hv

theorem Bounds.physical_prediction (B : Bounds) (D : Data) (hD : D.Valid)
    (hB : B.Sound D) (hC : B.Checks D) {x : Fin 3 → ℝ}
    (hx : Admissible (D.sigma:ℝ) x) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖(D.trajectory hD x hx).p t-D.position x t‖≤(B.positionError D:ℝ) ∧
      ‖(D.trajectory hD x hx).v t-D.velocity x t‖/(600*(D.alpha:ℝ))≤(B.velocityError D:ℝ) :=
  B.certifies D hD hB hC hx (D.trajectory hD x hx)

end
end GNC.OrbitalComparison.PointingCapRefinement
