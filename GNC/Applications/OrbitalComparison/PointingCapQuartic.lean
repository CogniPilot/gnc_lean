import GNC.Analysis.ParameterPolynomialDegree
import GNC.Applications.OrbitalComparison.PointingCapObstruction
import GNC.Applications.OrbitalComparison.PointingCapChart
import GNC.Applications.OrbitalComparison.PointingCapData.Taylor4Time12Burn1200

/-! The actual stored quartic, rather than a generator degree label, attains
one-centimetre physical prediction accuracy. The cubic obstruction proves
that its radial endpoint degree is exactly four. -/
namespace GNC.OrbitalComparison.PointingCapQuartic
open ParameterPolynomial PointingCapCertificate PointingCapBurn SpatialBurn Set
open PointingCapData.Taylor4Time12Burn1200
set_option maxHeartbeats 0

private theorem coefficients : ∀ j, ∀ a ∈ data.q j, a.c=0 ∧ a.u+a.v≤4 := by
  decide +kernel

noncomputable section

def polynomial (t : ℝ) (j : Fin 3) : MvPolynomial (Fin 2) ℝ :=
  transversePolynomial (data.q j) t

theorem degree (t : ℝ) (j : Fin 3) : (polynomial t j).totalDegree≤4 :=
  transversePolynomial_degree _ _ _ (fun a ha => (coefficients j a ha).2)

theorem polynomial_value (x : Fin 3 → ℝ) (t : ℝ) :
    WithLp.toLp 2 (fun j => MvPolynomial.eval ![x 0,x 1] (polynomial t j))=
      data.displacement x t := by
  have h (j : Fin 3) := transversePolynomial_value (data.q j) x t
    (fun a ha => (coefficients j a ha).1)
  ext j
  fin_cases j <;> simpa only [polynomial,Data.displacement,
    PointingCapPolynomial.vectorValue,pack_eq] using h _

theorem candidate_frame (x : Fin 3 → ℝ) :
    PointingCapObstruction.framed (data.position x 1)=data.displacement x 1 := by
  change HarmonicFrame.turn (-2)
    ((PointingCapFrame.reference 2 1+HarmonicFrame.turn (2*1) (data.displacement x 1))-
       PointingCapFrame.reference 2 1)=_
  simp only [mul_one,add_sub_cancel_left,PointingCapObstruction.turn_inverse]

/-- Every time in the burn is covered, with exact reference rotation. -/
theorem full_burn_accuracy {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    (X : Motion (data.alpha:ℝ) (direction x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-(PointingCapFrame.reference (data.alpha:ℝ) t+
      PointingCapFrame.turn (data.alpha:ℝ) t
        (WithLp.toLp 2 (fun j => MvPolynomial.eval ![x 0,x 1] (polynomial t j))))‖≤
          (data.positionError:ℝ) := by
  rw [polynomial_value]
  exact (data.certifies valid hx X t ht).1

theorem endpoint_accuracy {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    (X : Motion (data.alpha:ℝ) (direction x)) :
    ‖PointingCapObstruction.framed (X.p 1)-
      WithLp.toLp 2 (fun j => MvPolynomial.eval ![x 0,x 1] (polynomial 1 j))‖≤
        (data.positionError:ℝ) := by
  rw [polynomial_value,←candidate_frame,PointingCapObstruction.frame_difference]
  exact (data.certifies valid hx X 1 (by norm_num)).1

theorem meets_requirement : data.positionError≤PointingCapObstruction.positionRequirement_m :=
  position_limit.trans (by decide +kernel)

/-- The paper's independent transverse coordinates, with the forward radial
component reconstructed by the square root, cover the entire claimed disk. -/
theorem cap_accuracy {u v : ℝ} (h : u^2+v^2≤(data.sigma:ℝ)^2)
    (X : Motion (data.alpha:ℝ) (direction (PointingCapChart.input u v)))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-(PointingCapFrame.reference (data.alpha:ℝ) t+
      PointingCapFrame.turn (data.alpha:ℝ) t
        (WithLp.toLp 2 (fun j => MvPolynomial.eval ![u,v] (polynomial t j))))‖≤
          (PointingCapObstruction.positionRequirement_m:ℝ) := by
  have hx := PointingCapChart.admissible
    (show (data.sigma:ℝ)^2≤1 by change (((1/10:ℚ):ℝ))^2≤1; norm_num) h
  have he := full_burn_accuracy hx X ht
  have hb : (data.positionError:ℝ)≤(PointingCapObstruction.positionRequirement_m:ℝ) := by
    exact_mod_cast meets_requirement
  simpa only [PointingCapChart.input,Matrix.cons_val_zero,Matrix.cons_val_one] using he.trans hb

theorem cap_prediction {u v : ℝ} (h : u^2+v^2≤(data.sigma:ℝ)^2) :
    ∃ X : Motion (data.alpha:ℝ) (direction (PointingCapChart.input u v)),
      ∀ t ∈ Icc (0:ℝ) 1,
        ‖X.p t-(PointingCapFrame.reference (data.alpha:ℝ) t+
          PointingCapFrame.turn (data.alpha:ℝ) t
            (WithLp.toLp 2 (fun j => MvPolynomial.eval ![u,v] (polynomial t j))))‖≤
              (PointingCapObstruction.positionRequirement_m:ℝ) := by
  have hx := PointingCapChart.admissible
    (show (data.sigma:ℝ)^2≤1 by change (((1/10:ℚ):ℝ))^2≤1; norm_num) h
  exact ⟨data.trajectory valid _ hx,fun _ ht => cap_accuracy h _ ht⟩

theorem witness_accuracy (i : Fin 5) :
    ‖PointingCapObstruction.physicalDeviation i-
      WithLp.toLp 2 (fun j => MvPolynomial.eval ![(PointingCapObstruction.nodes i:ℝ),0]
        (polynomial 1 j))‖≤(PointingCapObstruction.positionRequirement_m:ℝ) := by
  have h := endpoint_accuracy (PointingCapObstruction.admissible i)
    (PointingCapData.ComponentTime12Burn1200.data.trajectory
      PointingCapData.ComponentTime12Burn1200.valid _ (PointingCapObstruction.admissible i))
  have h0 : PointingCapObstruction.inputs i 0=(PointingCapObstruction.nodes i:ℝ) := rfl
  have h1 : PointingCapObstruction.inputs i 1=0 := by
    fin_cases i <;> simp [PointingCapObstruction.inputs,PointingCapObstruction.points]
  have hb : (data.positionError:ℝ)≤(PointingCapObstruction.positionRequirement_m:ℝ) := by
    exact_mod_cast meets_requirement
  simpa only [PointingCapObstruction.physicalDeviation,h0,h1] using h.trans hb

/-- The quartic meets the requirement over the cap by `endpoint_accuracy`;
its radial degree cannot be smaller because of the physical obstruction. -/
theorem radial_degree : (polynomial 1 0).totalDegree=4 :=
  Nat.le_antisymm (degree 1 0) (PointingCapObstruction.required_degree _ witness_accuracy)

end
end GNC.OrbitalComparison.PointingCapQuartic
