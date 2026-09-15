import GNC.Analysis.ParameterPolynomialDegree
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerTime12Burn1200
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerTime13Burn1200
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerTime14Burn1200
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerTaylor4Time12Burn1200
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerTaylor4Time13Burn1200
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerTaylor6Time13Burn1200
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerTaylor6Time14Burn1200
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerAnchoredChebyshev4Response5Time12Burn1200
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerAnchoredChebyshev4Response5Time13Burn1200
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerAnchoredChebyshev4Response5Time14Burn1200
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerAnchoredChebyshev4Response6Time14Burn1200

/-! Matched physical accuracy after applying the same disk norm checker to
both representations. These are certificates for the existing coefficient
arrays, not new predictors. Graph counts and order selection are external
measurements; no global cost optimum is asserted. -/
namespace GNC.OrbitalComparison.PointingCapDiskComparison
open PointingCapCertificate PointingCapBurn PointingCapRefinement PointingCapDisk
open PointingCapDiskData Set
set_option maxHeartbeats 0

def Meets (D : Data) (B : Bounds) (position velocity : ℚ) : Prop :=
  B.positionError D≤position ∧ B.velocityError D≤velocity

theorem exact_3mm : Meets DiskHornerTime12Burn1200.original
    DiskHornerTime12Burn1200.bounds (3/1000) (1/10000) := by
  constructor
  · exact DiskHornerTime12Burn1200.position_limit.trans (by norm_num)
  · exact DiskHornerTime12Burn1200.velocity_limit.trans (by norm_num)

theorem exact_10mm : Meets DiskHornerTime12Burn1200.original
    DiskHornerTime12Burn1200.bounds (1/100) (1/10000) :=
  ⟨exact_3mm.1.trans (by norm_num),exact_3mm.2⟩

theorem polynomial_10mm : Meets DiskHornerTaylor4Time12Burn1200.original
    DiskHornerTaylor4Time12Burn1200.bounds (1/100) (1/10000) := by
  constructor
  · exact DiskHornerTaylor4Time12Burn1200.position_limit.trans (by norm_num)
  · exact DiskHornerTaylor4Time12Burn1200.velocity_limit.trans (by norm_num)

theorem polynomial_3mm : Meets DiskHornerAnchoredChebyshev4Response5Time12Burn1200.original
    DiskHornerAnchoredChebyshev4Response5Time12Burn1200.bounds (3/1000) (1/10000) := by
  constructor
  · exact DiskHornerAnchoredChebyshev4Response5Time12Burn1200.position_limit.trans (by norm_num)
  · exact DiskHornerAnchoredChebyshev4Response5Time12Burn1200.velocity_limit.trans (by norm_num)

theorem exact_half_mm : Meets DiskHornerTime14Burn1200.original
    DiskHornerTime14Burn1200.bounds (1/2000) (1/10000) := by
  constructor
  · exact DiskHornerTime14Burn1200.position_limit.trans (by norm_num)
  · exact DiskHornerTime14Burn1200.velocity_limit.trans (by norm_num)

theorem exact_1mm : Meets DiskHornerTime14Burn1200.original
    DiskHornerTime14Burn1200.bounds (1/1000) (1/10000) :=
  ⟨exact_half_mm.1.trans (by norm_num),exact_half_mm.2⟩

theorem polynomial_1mm : Meets DiskHornerAnchoredChebyshev4Response5Time13Burn1200.original
    DiskHornerAnchoredChebyshev4Response5Time13Burn1200.bounds (1/1000) (1/10000) := by
  constructor
  · exact DiskHornerAnchoredChebyshev4Response5Time13Burn1200.position_limit.trans (by norm_num)
  · exact DiskHornerAnchoredChebyshev4Response5Time13Burn1200.velocity_limit.trans (by norm_num)

theorem polynomial_half_mm : Meets DiskHornerAnchoredChebyshev4Response5Time14Burn1200.original
    DiskHornerAnchoredChebyshev4Response5Time14Burn1200.bounds (1/2000) (1/10000) := by
  constructor
  · exact DiskHornerAnchoredChebyshev4Response5Time14Burn1200.position_limit.trans (by norm_num)
  · exact DiskHornerAnchoredChebyshev4Response5Time14Burn1200.velocity_limit.trans (by norm_num)

theorem quintic13_coefficients : ∀ j,
    ∀ a ∈ DiskHornerAnchoredChebyshev4Response5Time13Burn1200.original.q j,
      a.c=0 ∧ a.u+a.v≤5 := by decide +kernel

theorem quintic14_coefficients : ∀ j,
    ∀ a ∈ DiskHornerAnchoredChebyshev4Response5Time14Burn1200.original.q j,
      a.c=0 ∧ a.u+a.v≤5 := by decide +kernel

noncomputable section

theorem quintic13_degree (t : ℝ) (j : Fin 3) :
    (ParameterPolynomial.transversePolynomial
      (DiskHornerAnchoredChebyshev4Response5Time13Burn1200.original.q j) t).totalDegree≤5 :=
  ParameterPolynomial.transversePolynomial_degree _ _ _ (fun a ha => (quintic13_coefficients j a ha).2)

theorem quintic14_degree (t : ℝ) (j : Fin 3) :
    (ParameterPolynomial.transversePolynomial
      (DiskHornerAnchoredChebyshev4Response5Time14Burn1200.original.q j) t).totalDegree≤5 :=
  ParameterPolynomial.transversePolynomial_degree _ _ _ (fun a ha => (quintic14_coefficients j a ha).2)

theorem meets_prediction (D : Data) (B : Bounds) (hD : D.Valid)
    (hB : B.Sound D) (hC : B.Checks D) {ep ev : ℚ} (hm : Meets D B ep ev)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x)
    (X : Motion (D.alpha:ℝ) (direction x)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-D.position x t‖≤(ep:ℝ) ∧
      ‖X.v t-D.velocity x t‖/(600*(D.alpha:ℝ))≤(ev:ℝ) := by
  have h := B.certifies D hD hB hC hx X t ht
  have hp : (B.positionError D:ℝ)≤(ep:ℝ) := by exact_mod_cast hm.1
  have hv : (B.velocityError D:ℝ)≤(ev:ℝ) := by exact_mod_cast hm.2
  exact ⟨h.1.trans hp,h.2.trans hv⟩

/-- The selected half-millimetre predictions enclose the same existing
physical solution for every admitted direction and all burn times. -/
theorem joint_half_mm {x : Fin 3 → ℝ} (hx : Admissible (1/10:ℝ) x) :
    ∃ X : Motion (2:ℝ) (direction x), ∀ t ∈ Icc (0:ℝ) 1,
      (‖X.p t-DiskHornerTime14Burn1200.original.position x t‖≤(1/2000:ℝ) ∧
       ‖X.v t-DiskHornerTime14Burn1200.original.velocity x t‖/1200≤(1/10000:ℝ)) ∧
      (‖X.p t-DiskHornerAnchoredChebyshev4Response5Time14Burn1200.original.position x t‖≤(1/2000:ℝ) ∧
       ‖X.v t-DiskHornerAnchoredChebyshev4Response5Time14Burn1200.original.velocity x t‖/1200≤(1/10000:ℝ)) := by
  have hxE : Admissible (DiskHornerTime14Burn1200.original.sigma:ℝ) x := by
    simpa [DiskHornerTime14Burn1200.original,PointingCapData.HornerTime14Burn1200.data] using hx
  have hxP : Admissible (DiskHornerAnchoredChebyshev4Response5Time14Burn1200.original.sigma:ℝ) x := by
    simpa [DiskHornerAnchoredChebyshev4Response5Time14Burn1200.original,
      PointingCapData.HornerAnchoredChebyshev4Response5Time14Burn1200.data] using hx
  have hsE : (600:ℝ)*(DiskHornerTime14Burn1200.original.alpha:ℝ)=1200 := by norm_num [
    DiskHornerTime14Burn1200.original,PointingCapData.HornerTime14Burn1200.data]
  have hsP : (600:ℝ)*(DiskHornerAnchoredChebyshev4Response5Time14Burn1200.original.alpha:ℝ)=1200 := by norm_num [
    DiskHornerAnchoredChebyshev4Response5Time14Burn1200.original,
    PointingCapData.HornerAnchoredChebyshev4Response5Time14Burn1200.data]
  let X := DiskHornerTime14Burn1200.original.trajectory PointingCapData.HornerTime14Burn1200.valid x hxE
  refine ⟨X,?_⟩
  intro t ht
  constructor
  · convert meets_prediction _ _ PointingCapData.HornerTime14Burn1200.valid
      (DiskHornerTime14Burn1200.models.refinedBounds_sound _ PointingCapData.HornerTime14Burn1200.valid
        DiskHornerTime14Burn1200.valid) DiskHornerTime14Burn1200.checks exact_half_mm hxE X t ht
      using 1 <;> norm_num [hsE]
  · convert meets_prediction _ _ PointingCapData.HornerAnchoredChebyshev4Response5Time14Burn1200.valid
      (DiskHornerAnchoredChebyshev4Response5Time14Burn1200.models.refinedBounds_sound _
        PointingCapData.HornerAnchoredChebyshev4Response5Time14Burn1200.valid
        DiskHornerAnchoredChebyshev4Response5Time14Burn1200.valid)
      DiskHornerAnchoredChebyshev4Response5Time14Burn1200.checks polynomial_half_mm hxP X t ht
      using 1 <;> norm_num [hsP]

end
end GNC.OrbitalComparison.PointingCapDiskComparison
