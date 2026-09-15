import GNC.Analysis.PointingQuery
import GNC.Applications.OrbitalComparison.PointingCapGeometryCompression
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerTaylor4Time12Burn1200

/-! A factored quartic query bound to the actual certified coefficient record.
The radius is shared between outputs. The comparison counts repeated pointing
queries with prepared time coefficients; offline proof/construction, direction
construction, frame reconstruction and floating-point roundoff are separate. -/
namespace GNC.OrbitalComparison.PointingCapQueryComparison
open ParameterPolynomial PointingCapCertificate PointingCapBurn SpatialBurn Set
open PointingCapDiskData.DiskHornerTaylor4Time12Burn1200
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev data := PointingCapData.HornerTaylor4Time12Burn1200.data

def curve (i : Fin 3) (u v : ℕ) : List ℚ :=
  (((data.q i).find? fun a => a.u=u && a.v=v && a.c=0).getD ⟨0,0,0,[]⟩).time

/-- The subtraction is prepared with the time coefficients, before queries. -/
def difference (i : Fin 3) : List ℚ :=
  PolynomialBounds.subtract (curve i 2 0) (curve i 0 2)

def planarPolynomial (i : Fin 3) : Coefficients :=
  [⟨1,0,0,curve i 1 0⟩,
   ⟨2,0,0,PolynomialBounds.add (difference i) (curve i 0 2)⟩,
   ⟨0,2,0,curve i 0 2⟩,
   ⟨3,0,0,curve i 3 0⟩,⟨1,2,0,curve i 3 0⟩,
   ⟨4,0,0,curve i 4 0⟩,⟨2,2,0,PolynomialBounds.scale 2 (curve i 4 0)⟩,
   ⟨0,4,0,curve i 4 0⟩]

def normalPolynomial : Coefficients :=
  [⟨0,1,0,curve 2 0 1⟩,⟨1,1,0,curve 2 1 1⟩,
   ⟨2,1,0,curve 2 0 3⟩,⟨0,3,0,curve 2 0 3⟩]

def factored : PointingCapPolynomial.Vector :=
  ![planarPolynomial 0,planarPolynomial 1,normalPolynomial]

/-- Coefficient equality for the entire time polynomial, not just burnout. -/
theorem factorization : ∀ i, zero (subtract (data.q i) (factored i)) := by
  decide +kernel

noncomputable section

def queryPlanar (i : Fin 3) (u h t : ℝ) : Planning.FlopKernel.Value ℝ :=
  PointingQuery.planar u h (PolynomialOrder.value (curve i 1 0) t)
    (PolynomialOrder.value (difference i) t) (PolynomialOrder.value (curve i 0 2) t)
    (PolynomialOrder.value (curve i 4 0) t) (PolynomialOrder.value (curve i 3 0) t)

def queryNormal (u v h t : ℝ) : Planning.FlopKernel.Value ℝ :=
  PointingQuery.normal u v h (PolynomialOrder.value (curve 2 0 1) t)
    (PolynomialOrder.value (curve 2 1 1) t) (PolynomialOrder.value (curve 2 0 3) t)

def query (x : Fin 3 → ℝ) (t : ℝ) : Fin 3 → Planning.FlopKernel.Value ℝ :=
  let h := (PointingQuery.radiusSquared (x 0) (x 1)).value
  ![queryPlanar 0 (x 0) h t,queryPlanar 1 (x 0) h t,queryNormal (x 0) (x 1) h t]

theorem query_factorization (x : Fin 3 → ℝ) (t : ℝ) :
    WithLp.toLp 2 (fun i => (query x t i).value)=
      PointingCapPolynomial.vectorValue factored x t := by
  ext i
  fin_cases i <;>
    simp [query,queryPlanar,queryNormal,PointingQuery.planar_value,PointingQuery.normal_value,
      PointingQuery.radiusSquared_value,PointingCapPolynomial.vectorValue,pack_eq,
      factored,planarPolynomial,normalPolynomial,value,termValue,monomial,
      PolynomialOrder.value_add,PolynomialOrder.value_scale] <;> ring

theorem query_matches (x : Fin 3 → ℝ) (t : ℝ) :
    WithLp.toLp 2 (fun i => (query x t i).value)=data.displacement x t := by
  rw [query_factorization]
  have h (i : Fin 3) := ParameterPolynomial.identity _ _ (factorization i) x t
  simp only [Data.displacement,PointingCapPolynomial.vectorValue,h]

/-- Charge one shared squared radius plus the three factored outputs. -/
theorem query_flops (x : Fin 3 → ℝ) (t : ℝ) :
    (PointingQuery.radiusSquared (x 0) (x 1)).flops+
      (∑ i, (query x t i).flops)=26 := by
  rw [Fin.sum_univ_three]
  rfl

theorem physical_bound {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    (X : Motion (data.alpha:ℝ) (direction x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-(PointingCapFrame.reference (data.alpha:ℝ) t+
      PointingCapFrame.turn (data.alpha:ℝ) t
        (WithLp.toLp 2 (fun i => (query x t i).value)))‖≤(4045377/1000000000:ℝ) := by
  rw [query_matches]
  have hp := (bounds.certifies data PointingCapData.HornerTaylor4Time12Burn1200.valid
    (models.refinedBounds_sound original PointingCapData.HornerTaylor4Time12Burn1200.valid valid)
      checks hx X t ht).1
  have hl : (bounds.positionError data:ℝ)≤((4045377/1000000000:ℚ):ℝ) := by
    exact_mod_cast position_limit
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hl
  exact hp.trans hl

def queryWithDepth (x : Fin 3 → ℝ) (t : ℝ) : Fin 3 → Planning.FlopKernel.Value ℝ :=
  let h := (PointingQuery.radiusFromDepth (x 2)).value
  ![queryPlanar 0 (x 0) h t,queryPlanar 1 (x 0) h t,queryNormal (x 0) (x 1) h t]

theorem queryWithDepth_eq {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x) (t : ℝ) :
    queryWithDepth x t=query x t := by
  have he : (PointingQuery.radiusFromDepth (x 2)).value=
      (PointingQuery.radiusSquared (x 0) (x 1)).value := by
    rw [PointingQuery.radiusFromDepth_value,PointingQuery.radiusSquared_value]
    nlinarith [hx.2.2.1]
  simp only [queryWithDepth,query,he]

theorem queryWithDepth_flops (x : Fin 3 → ℝ) (t : ℝ) :
    (PointingQuery.radiusFromDepth (x 2)).flops+
      (∑ i, (queryWithDepth x t i).flops)=25 := by
  rw [Fin.sum_univ_three]
  rfl

theorem queryWithDepth_physical_bound {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    (X : Motion (data.alpha:ℝ) (direction x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-(PointingCapFrame.reference (data.alpha:ℝ) t+
      PointingCapFrame.turn (data.alpha:ℝ) t
        (WithLp.toLp 2 (fun i => (queryWithDepth x t i).value)))‖≤(4045377/1000000000:ℝ) := by
  rw [queryWithDepth_eq hx]
  exact physical_bound hx X ht

/-- Both certified arithmetic queries meet the same one-centimetre target;
the quartic has the smaller error bound. No cost optimality is asserted. -/
theorem target_and_cost (x : Fin 3 → ℝ) (t : ℝ) :
    PointingCapGeometryCompression.displayError<1/100 ∧
    (4045377/1000000000:ℚ)<1/100 ∧
    (∑ i, (PointingCapGeometryCompression.query x t i).flops)=11 ∧
    (PointingQuery.radiusFromDepth (x 2)).flops+
      (∑ i, (queryWithDepth x t i).flops)=25 :=
  ⟨PointingCapGeometryCompression.meets_centimetre,by norm_num,
    PointingCapGeometryCompression.query_flops x t,queryWithDepth_flops x t⟩

end
end GNC.OrbitalComparison.PointingCapQueryComparison
