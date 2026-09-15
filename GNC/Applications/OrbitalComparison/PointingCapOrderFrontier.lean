import GNC.Applications.OrbitalComparison.HornerGraph
import GNC.Applications.OrbitalComparison.PointingCapData.HornerTime13Burn1200
import GNC.Applications.OrbitalComparison.PointingCapData.HornerTime14Burn1200
import GNC.Applications.OrbitalComparison.PointingCapData.HornerTaylor4Time13Burn1200
import GNC.Applications.OrbitalComparison.PointingCapData.HornerTaylor6Time13Burn1200
import GNC.Applications.OrbitalComparison.PointingCapData.HornerTaylor6Time14Burn1200
import GNC.Applications.OrbitalComparison.PointingCapData.HornerAnchoredChebyshev4Response6Time14Burn1200
import GNC.Applications.OrbitalComparison.PointingCapData.HornerAnchoredChebyshev4Response5Time12Burn1200

/-! Selected physical certificates after varying both time and transverse
orders. All compared records describe the same 1200 s pointing-cap family.
The external graph counts and the optimizer's selection are not Lean
complexity or global-optimality theorems. -/
namespace GNC.OrbitalComparison.PointingCapOrderFrontier
open PointingCapCertificate PointingCapBurn PointingCapData Set
set_option maxHeartbeats 0

def Meets (D : Data) (position velocity : ℚ) : Prop :=
  D.positionError≤position ∧ D.velocityError≤velocity

theorem exact_10mm : Meets HornerTime12Burn1200.data (1/100) (1/10000) := by
  constructor
  · exact HornerTime12Burn1200.position_limit.trans (by norm_num)
  · exact HornerTime12Burn1200.velocity_limit.trans (by norm_num)

theorem polynomial_10mm : Meets HornerTaylor4Time12Burn1200.data (1/100) (1/10000) := by
  constructor
  · exact HornerTaylor4Time12Burn1200.position_limit.trans (by norm_num)
  · exact HornerTaylor4Time12Burn1200.velocity_limit.trans (by norm_num)

theorem exact_3mm : Meets HornerTime13Burn1200.data (3/1000) (1/10000) := by
  constructor
  · exact HornerTime13Burn1200.position_limit.trans (by norm_num)
  · exact HornerTime13Burn1200.velocity_limit.trans (by norm_num)

theorem taylor_3mm : Meets HornerTaylor4Time13Burn1200.data (3/1000) (1/10000) := by
  constructor
  · exact HornerTaylor4Time13Burn1200.position_limit.trans (by norm_num)
  · exact HornerTaylor4Time13Burn1200.velocity_limit.trans (by norm_num)

theorem polynomial_3mm : Meets HornerAnchoredChebyshev4Response5Time12Burn1200.data (3/1000) (1/10000) := by
  constructor
  · exact HornerAnchoredChebyshev4Response5Time12Burn1200.position_limit.trans (by norm_num)
  · exact HornerAnchoredChebyshev4Response5Time12Burn1200.velocity_limit.trans (by norm_num)

theorem quintic_coefficients : ∀ j,
    ∀ a ∈ HornerAnchoredChebyshev4Response5Time12Burn1200.data.q j, a.c=0 ∧ a.u+a.v≤5 := by
  decide +kernel

theorem exact_half_mm : Meets HornerTime14Burn1200.data (1/2000) (1/10000) := by
  constructor
  · exact HornerTime14Burn1200.position_limit.trans (by norm_num)
  · exact HornerTime14Burn1200.velocity_limit.trans (by norm_num)

theorem polynomial_1mm : Meets HornerTaylor6Time13Burn1200.data (1/1000) (1/10000) := by
  constructor
  · exact HornerTaylor6Time13Burn1200.position_limit.trans (by norm_num)
  · exact HornerTaylor6Time13Burn1200.velocity_limit.trans (by norm_num)

theorem taylor_half_mm : Meets HornerTaylor6Time14Burn1200.data (1/2000) (1/10000) := by
  constructor
  · exact HornerTaylor6Time14Burn1200.position_limit.trans (by norm_num)
  · exact HornerTaylor6Time14Burn1200.velocity_limit.trans (by norm_num)

theorem polynomial_half_mm : Meets HornerAnchoredChebyshev4Response6Time14Burn1200.data (1/2000) (1/10000) := by
  constructor
  · exact HornerAnchoredChebyshev4Response6Time14Burn1200.position_limit.trans (by norm_num)
  · exact HornerAnchoredChebyshev4Response6Time14Burn1200.velocity_limit.trans (by norm_num)

theorem anchored_coefficients : ∀ j,
    ∀ a ∈ HornerAnchoredChebyshev4Response6Time14Burn1200.data.q j, a.c=0 ∧ a.u+a.v≤6 := by
  decide +kernel

theorem sextic13_coefficients : ∀ j,
    ∀ a ∈ HornerTaylor6Time13Burn1200.data.q j, a.c=0 ∧ a.u+a.v≤6 := by
  decide +kernel

theorem sextic14_coefficients : ∀ j,
    ∀ a ∈ HornerTaylor6Time14Burn1200.data.q j, a.c=0 ∧ a.u+a.v≤6 := by
  decide +kernel

noncomputable section

theorem quintic_degree (t : ℝ) (j : Fin 3) :
    (ParameterPolynomial.transversePolynomial
      (HornerAnchoredChebyshev4Response5Time12Burn1200.data.q j) t).totalDegree≤5 :=
  ParameterPolynomial.transversePolynomial_degree _ _ _ (fun a ha => (quintic_coefficients j a ha).2)

theorem anchored_degree (t : ℝ) (j : Fin 3) :
    (ParameterPolynomial.transversePolynomial
      (HornerAnchoredChebyshev4Response6Time14Burn1200.data.q j) t).totalDegree≤6 :=
  ParameterPolynomial.transversePolynomial_degree _ _ _ (fun a ha => (anchored_coefficients j a ha).2)

theorem sextic13_degree (t : ℝ) (j : Fin 3) :
    (ParameterPolynomial.transversePolynomial (HornerTaylor6Time13Burn1200.data.q j) t).totalDegree≤6 :=
  ParameterPolynomial.transversePolynomial_degree _ _ _ (fun a ha => (sextic13_coefficients j a ha).2)

theorem sextic14_degree (t : ℝ) (j : Fin 3) :
    (ParameterPolynomial.transversePolynomial (HornerTaylor6Time14Burn1200.data.q j) t).totalDegree≤6 :=
  ParameterPolynomial.transversePolynomial_degree _ _ _ (fun a ha => (sextic14_coefficients j a ha).2)

theorem meets_prediction (D : Data) (hv : D.Valid) {ep ev : ℚ} (hm : Meets D ep ev)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x)
    (X : Motion (D.alpha:ℝ) (direction x)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-D.position x t‖≤(ep:ℝ) ∧
      ‖X.v t-D.velocity x t‖/(600*(D.alpha:ℝ))≤(ev:ℝ) := by
  have h := D.certifies hv hx X t ht
  have hp : (D.positionError:ℝ)≤(ep:ℝ) := by exact_mod_cast hm.1
  have he : (D.velocityError:ℝ)≤(ev:ℝ) := by exact_mod_cast hm.2
  exact ⟨h.1.trans hp,h.2.trans he⟩

/-- Both half-millimetre certificates apply to a single existing physical
trajectory, for every direction in the disk and throughout the burn. -/
theorem joint_half_mm {x : Fin 3 → ℝ} (hx : Admissible (1/10:ℝ) x) :
    ∃ X : Motion (2:ℝ) (direction x), ∀ t ∈ Icc (0:ℝ) 1,
      (‖X.p t-HornerTime14Burn1200.data.position x t‖≤(1/2000:ℝ) ∧
       ‖X.v t-HornerTime14Burn1200.data.velocity x t‖/1200≤(1/10000:ℝ)) ∧
      (‖X.p t-HornerAnchoredChebyshev4Response6Time14Burn1200.data.position x t‖≤(1/2000:ℝ) ∧
       ‖X.v t-HornerAnchoredChebyshev4Response6Time14Burn1200.data.velocity x t‖/1200≤(1/10000:ℝ)) := by
  have hxE : Admissible (HornerTime14Burn1200.data.sigma:ℝ) x := by
    simpa [HornerTime14Burn1200.data] using hx
  have hxP : Admissible (HornerAnchoredChebyshev4Response6Time14Burn1200.data.sigma:ℝ) x := by
    simpa [HornerAnchoredChebyshev4Response6Time14Burn1200.data] using hx
  have hscaleE : (600:ℝ)*(HornerTime14Burn1200.data.alpha:ℝ)=1200 := by
    norm_num [HornerTime14Burn1200.data]
  have hscaleP : (600:ℝ)*(HornerAnchoredChebyshev4Response6Time14Burn1200.data.alpha:ℝ)=1200 := by
    norm_num [HornerAnchoredChebyshev4Response6Time14Burn1200.data]
  let X := HornerTime14Burn1200.data.trajectory HornerTime14Burn1200.valid x hxE
  refine ⟨X,?_⟩
  intro t ht
  constructor
  · convert meets_prediction _ HornerTime14Burn1200.valid exact_half_mm hxE X t ht using 1 <;> norm_num [hscaleE]
  · convert meets_prediction _ HornerAnchoredChebyshev4Response6Time14Burn1200.valid polynomial_half_mm hxP X t ht using 1 <;> norm_num [hscaleP]

end
end GNC.OrbitalComparison.PointingCapOrderFrontier
