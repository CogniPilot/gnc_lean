import GNC.Analysis.CircleQuery
import GNC.Applications.OrbitalComparison.SpatialFieldCertificate

/-! Physical position and inertial-velocity boxes at a specified rational
epoch within the certified burn. Exact polynomial specialization subtracts
the shared computed nominal before bounding the pointing interval. The
physical certificate charges both actual trajectories. No angle sampling
or floating-point query evaluator is assumed. -/
namespace GNC.OrbitalComparison.SpatialTerminalCertificate
open SpatialFieldCertificate SpatialBurn Set
noncomputable section

theorem position_component (q : Fin 3 → CirclePolynomial.Coefficients)
    (θ t : ℝ) (i : Fin 3) :
    (position SpatialSources.circle q θ t) i = 7000000*CirclePolynomial.value (q i) t θ := by
  change ((7000000:ℝ) • pack (CirclePolynomial.value (q 0) t θ)
    (CirclePolynomial.value (q 1) t θ) (CirclePolynomial.value (q 2) t θ)) i = _
  fin_cases i <;> simp [pack_eq]

theorem candidate_component (q : Fin 3 → CirclePolynomial.Coefficients)
    (t a : ℚ) {θ : ℝ} (hθ : |θ| ≤ (a:ℝ)) (i : Fin 3) :
    |(position SpatialSources.circle q θ (t:ℝ)-
        position SpatialSources.circle q 0 (t:ℝ)) i| ≤
      (7000000*CircleQuery.radius (q i) t a:ℚ) := by
  change |(position SpatialSources.circle q θ (t:ℝ)) i-
    (position SpatialSources.circle q 0 (t:ℝ)) i| ≤ _
  rw [position_component,position_component,← mul_sub,abs_mul]
  norm_num only [Rat.cast_mul,Rat.cast_ofNat,abs_of_pos (by norm_num : (0:ℝ) < 7000000)]
  exact mul_le_mul_of_nonneg_left (CircleQuery.radius_sound (q i) t a hθ) (by norm_num)

theorem physical_component (q : Fin 3 → CirclePolynomial.Coefficients)
    (x y : E3) (t a : ℚ) {θ ε : ℝ} (hθ : |θ| ≤ (a:ℝ))
    (herror : ‖(x-y)-(position SpatialSources.circle q θ (t:ℝ)-
      position SpatialSources.circle q 0 (t:ℝ))‖ ≤ ε) (i : Fin 3) :
    |(x-y) i| ≤ (7000000*CircleQuery.radius (q i) t a:ℚ)+ε := by
  let c := position SpatialSources.circle q θ (t:ℝ)-position SpatialSources.circle q 0 (t:ℝ)
  have hc := (PiLp.norm_apply_le ((x-y)-c) i).trans herror
  change ‖(x-y) i-c i‖ ≤ ε at hc
  rw [Real.norm_eq_abs] at hc
  have hp := candidate_component q t a hθ i
  have hh := abs_add_le ((x-y) i-c i) (c i)
  rw [sub_add_cancel] at hh
  linarith

end

def positionRadius (D : Data (C := CirclePolynomial.Coefficients)) (t a : ℚ) (i : Fin 3) : ℚ :=
  7000000*CircleQuery.radius (D.q i) t a+2*D.positionLimit

def velocityRadius (D : Data (C := CirclePolynomial.Coefficients)) (t a : ℚ) (i : Fin 3) : ℚ :=
  (7000000/600)*CircleQuery.radius (CirclePolynomial.derivative (D.q i)) t a+2*D.velocityLimit

noncomputable section

/-- Whole pointing family, at any specified time in the burn. Velocity is
in metres per second, not the derivative of a rotating coordinate. -/
theorem relative_bounds (D : Data (C := CirclePolynomial.Coefficients)) (mode : Law)
    (hD : D.Valid SpatialSources.circle WeightedCertificate.circleTime mode)
    {θ : ℝ} (X : PhysicalOrbit mode θ) (X₀ : PhysicalOrbit mode 0)
    (t a : ℚ) (ht : (t:ℝ) ∈ Icc (0:ℝ) 1)
    (ha : a ≤ UniformCertificate.angle) (hθ : |θ| ≤ (a:ℝ)) (i : Fin 3) :
    |(X.p (t:ℝ)-X₀.p (t:ℝ)) i| ≤ (positionRadius D t a i:ℝ) ∧
    |(X.v (t:ℝ)-X₀.v (t:ℝ)) i|/600 ≤ (velocityRadius D t a i:ℝ) := by
  have hθ' : |θ| ≤ (UniformCertificate.angle:ℝ) := hθ.trans (by exact_mod_cast ha)
  have h := D.relative_certifies SpatialSources.circle WeightedCertificate.circleTime mode hD X X₀ hθ' (t:ℝ) ht
  constructor
  · have hp := physical_component D.q (X.p (t:ℝ)) (X₀.p (t:ℝ)) t a hθ h.1 i
    simpa [positionRadius] using hp
  · have hv : ‖(X.v (t:ℝ)-X₀.v (t:ℝ))-
        (velocity SpatialSources.circle D.q θ (t:ℝ)-velocity SpatialSources.circle D.q 0 (t:ℝ))‖ ≤
          600*(2*(D.velocityLimit:ℝ)) := by linarith [h.2]
    have hb := physical_component (fun j => CirclePolynomial.derivative (D.q j))
      (X.v (t:ℝ)) (X₀.v (t:ℝ)) t a hθ hv i
    have hd := div_le_div_of_nonneg_right hb (by norm_num : (0:ℝ) ≤ 600)
    convert hd using 1
    simp only [velocityRadius,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat]
    ring

end
end GNC.OrbitalComparison.SpatialTerminalCertificate
