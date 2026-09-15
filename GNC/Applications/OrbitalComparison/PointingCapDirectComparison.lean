import GNC.Analysis.ReducedSphereResponse
import GNC.Analysis.PointingQuery
import GNC.Applications.OrbitalComparison.PointingCapTimeData.DirectTime11Burn1200
import GNC.Applications.OrbitalComparison.PointingCapTimeData.ProfileComponentTime10Burn1200
import GNC.Applications.OrbitalComparison.PointingCapTimeData.ProfileTaylor4Time10Burn1200

/-! Counted queries for three directly checked physical coefficient records.
All use prepared time coefficients and physical direction components.
Generation, certificate construction, frame reconstruction and floating-point
execution are separate from the proved scalar query operation counts. -/
namespace GNC.OrbitalComparison.PointingCapDirectComparison
open ParameterPolynomial PointingCapCertificate PointingCapBurn SpatialBurn Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curve (D : Data) (i : Fin 3) (u v c : ℕ) : List ℚ :=
  (((D.q i).find? fun a => a.u=u && a.v=v && a.c=c).getD ⟨0,0,0,[]⟩).time

namespace Direct
abbrev data := PointingCapData.DirectTime11Burn1200.data

def planar (i : Fin 3) : Coefficients :=
  [⟨1,0,0,curve data i 1 0 0⟩,⟨0,0,1,curve data i 0 0 1⟩,⟨2,0,0,curve data i 2 0 0⟩]
def normal : Coefficients := [⟨0,1,0,curve data 2 0 1 0⟩,⟨1,1,0,curve data 2 1 1 0⟩]
def factored : PointingCapPolynomial.Vector := ![planar 0,planar 1,normal]
theorem factorization : ∀ i, zero (subtract (data.q i) (factored i)) := by decide +kernel

noncomputable section
def coefficient (i : Fin 3) (u v c : ℕ) (t : ℝ) := PolynomialOrder.value (curve data i u v c) t
def query (x : Fin 3 → ℝ) (t : ℝ) : Fin 3 → Planning.FlopKernel.Value ℝ :=
  ![SphereRankOne.queryComponent (x 0) (x 2)
      (coefficient 0 1 0 0 t) (coefficient 0 0 0 1 t) (coefficient 0 2 0 0 t),
    SphereRankOne.queryComponent (x 0) (x 2)
      (coefficient 1 1 0 0 t) (coefficient 1 0 0 1 t) (coefficient 1 2 0 0 t),
    ReducedSphereResponse.queryNormal (x 0) (x 1)
      (coefficient 2 0 1 0 t) (coefficient 2 1 1 0 t)]

theorem query_matches (x : Fin 3 → ℝ) (t : ℝ) :
    WithLp.toLp 2 (fun i => (query x t i).value)=data.displacement x t := by
  have h (i : Fin 3) := ParameterPolynomial.identity _ _ (factorization i) x t
  simp only [Data.displacement,PointingCapPolynomial.vectorValue,h]
  ext i
  fin_cases i <;>
    simp [query,coefficient,SphereRankOne.queryComponent_value,ReducedSphereResponse.queryNormal_value,
      factored,planar,normal,pack_eq,value,termValue,monomial] <;> ring

theorem query_flops (x : Fin 3 → ℝ) (t : ℝ) : (∑ i, (query x t i).flops)=13 := by
  rw [Fin.sum_univ_three]
  rfl

theorem physical_bound {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    (X : Motion (data.alpha:ℝ) (direction x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-(PointingCapFrame.reference (data.alpha:ℝ) t+
      PointingCapFrame.turn (data.alpha:ℝ) t
        (WithLp.toLp 2 (fun i => (query x t i).value)))‖≤(1114279/125000000:ℝ) := by
  rw [query_matches]
  exact (PointingCapTimeData.DirectTime11Burn1200.prediction hx X t ht).1

end
end Direct

namespace Component
abbrev data := PointingCapData.ProfileComponentTime10Burn1200.data
def difference (i : Fin 3) : List ℚ :=
  PolynomialBounds.subtract (curve data i 2 0 0) (curve data i 0 2 0)
def axial (i : Fin 3) : List ℚ :=
  PolynomialBounds.add (curve data i 0 0 1) (PolynomialBounds.scale 2 (curve data i 0 2 0))
def planar (i : Fin 3) : Coefficients :=
  [⟨1,0,0,curve data i 1 0 0⟩,⟨0,0,1,curve data i 0 0 1⟩,
   ⟨2,0,0,curve data i 2 0 0⟩,⟨0,2,0,curve data i 0 2 0⟩,⟨1,0,1,curve data i 1 0 1⟩]
def normal : Coefficients :=
  [⟨0,1,0,curve data 2 0 1 0⟩,⟨1,1,0,curve data 2 1 1 0⟩,⟨0,1,1,curve data 2 0 1 1⟩]
def factored : PointingCapPolynomial.Vector := ![planar 0,planar 1,normal]
theorem factorization : ∀ i, zero (subtract (data.q i) (factored i)) := by decide +kernel

noncomputable section
def coefficient (i : Fin 3) (u v c : ℕ) (t : ℝ) := PolynomialOrder.value (curve data i u v c) t
def queryPlanar (i : Fin 3) (u c t : ℝ) : Planning.FlopKernel.Value ℝ :=
  let L := coefficient i 1 0 0 t
  let Q := PolynomialOrder.value (difference i) t
  let D := coefficient i 1 0 1 t
  let C := PolynomialOrder.value (axial i) t
  let B := coefficient i 0 2 0 t
  Planning.FlopKernel.add
    (Planning.FlopKernel.mul (Planning.FlopKernel.input u)
      (Planning.FlopKernel.add
        (Planning.FlopKernel.add (Planning.FlopKernel.input L)
          (Planning.FlopKernel.mul (Planning.FlopKernel.input u) (Planning.FlopKernel.input Q)))
        (Planning.FlopKernel.mul (Planning.FlopKernel.input c) (Planning.FlopKernel.input D))))
    (Planning.FlopKernel.mul (Planning.FlopKernel.input c)
      (PointingQuery.subtract (Planning.FlopKernel.input C)
        (Planning.FlopKernel.mul (Planning.FlopKernel.input c) (Planning.FlopKernel.input B))))
def query (x : Fin 3 → ℝ) (t : ℝ) : Fin 3 → Planning.FlopKernel.Value ℝ :=
  ![queryPlanar 0 (x 0) (x 2) t,queryPlanar 1 (x 0) (x 2) t,
    PointingQuery.normal (x 0) (x 1) (x 2)
      (coefficient 2 0 1 0 t) (coefficient 2 1 1 0 t) (coefficient 2 0 1 1 t)]

theorem query_matches {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x) (t : ℝ) :
    WithLp.toLp 2 (fun i => (query x t i).value)=data.displacement x t := by
  have hv : x 1^2=2*x 2-x 2^2-x 0^2 := by linarith [hx.2.2.1]
  have h (i : Fin 3) := ParameterPolynomial.identity _ _ (factorization i) x t
  simp only [Data.displacement,PointingCapPolynomial.vectorValue,h]
  ext i
  fin_cases i <;>
    simp [query,queryPlanar,coefficient,axial,difference,PointingQuery.normal_value,
      PointingQuery.subtract,Planning.FlopKernel.add,Planning.FlopKernel.mul,Planning.FlopKernel.input,
      factored,planar,normal,pack_eq,value,termValue,monomial,hv,
      PolynomialOrder.value_add,PolynomialOrder.value_subtract,PolynomialOrder.value_scale] <;> ring

theorem query_flops (x : Fin 3 → ℝ) (t : ℝ) : (∑ i, (query x t i).flops)=23 := by
  rw [Fin.sum_univ_three]
  rfl

theorem physical_bound {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    (X : Motion (data.alpha:ℝ) (direction x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-(PointingCapFrame.reference (data.alpha:ℝ) t+
      PointingCapFrame.turn (data.alpha:ℝ) t
        (WithLp.toLp 2 (fun i => (query x t i).value)))‖≤(2016289/1000000000:ℝ) := by
  rw [query_matches hx]
  exact (PointingCapTimeData.ProfileComponentTime10Burn1200.prediction hx X t ht).1
end
end Component

namespace Quartic
abbrev data := PointingCapData.ProfileTaylor4Time10Burn1200.data
def difference (i : Fin 3) : List ℚ :=
  PolynomialBounds.subtract (curve data i 2 0 0) (curve data i 0 2 0)
def planar (i : Fin 3) : Coefficients :=
  [⟨1,0,0,curve data i 1 0 0⟩,
   ⟨2,0,0,PolynomialBounds.add (difference i) (curve data i 0 2 0)⟩,
   ⟨0,2,0,curve data i 0 2 0⟩,
   ⟨3,0,0,curve data i 3 0 0⟩,⟨1,2,0,curve data i 3 0 0⟩,
   ⟨4,0,0,curve data i 4 0 0⟩,⟨2,2,0,PolynomialBounds.scale 2 (curve data i 4 0 0)⟩,
   ⟨0,4,0,curve data i 4 0 0⟩]
def normal : Coefficients :=
  [⟨0,1,0,curve data 2 0 1 0⟩,⟨1,1,0,curve data 2 1 1 0⟩,
   ⟨2,1,0,curve data 2 0 3 0⟩,⟨0,3,0,curve data 2 0 3 0⟩]
def factored : PointingCapPolynomial.Vector := ![planar 0,planar 1,normal]
theorem factorization : ∀ i, zero (subtract (data.q i) (factored i)) := by decide +kernel

noncomputable section
def coefficient (i : Fin 3) (u v : ℕ) (t : ℝ) := PolynomialOrder.value (curve data i u v 0) t
def queryPlanar (i : Fin 3) (u h t : ℝ) : Planning.FlopKernel.Value ℝ :=
  PointingQuery.planar u h (coefficient i 1 0 t) (PolynomialOrder.value (difference i) t)
    (coefficient i 0 2 t) (coefficient i 4 0 t) (coefficient i 3 0 t)
def queryNormal (u v h t : ℝ) : Planning.FlopKernel.Value ℝ :=
  PointingQuery.normal u v h (coefficient 2 0 1 t) (coefficient 2 1 1 t) (coefficient 2 0 3 t)
def query (x : Fin 3 → ℝ) (t : ℝ) : Fin 3 → Planning.FlopKernel.Value ℝ :=
  let h := (PointingQuery.radiusFromDepth (x 2)).value
  ![queryPlanar 0 (x 0) h t,queryPlanar 1 (x 0) h t,queryNormal (x 0) (x 1) h t]

theorem query_matches {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x) (t : ℝ) :
    WithLp.toLp 2 (fun i => (query x t i).value)=data.displacement x t := by
  have he : (PointingQuery.radiusFromDepth (x 2)).value=
      (PointingQuery.radiusSquared (x 0) (x 1)).value := by
    rw [PointingQuery.radiusFromDepth_value,PointingQuery.radiusSquared_value]
    nlinarith [hx.2.2.1]
  have h (i : Fin 3) := ParameterPolynomial.identity _ _ (factorization i) x t
  simp only [query,he,Data.displacement,PointingCapPolynomial.vectorValue,h]
  ext i
  fin_cases i <;>
    simp [queryPlanar,queryNormal,coefficient,PointingQuery.planar_value,PointingQuery.normal_value,
      PointingQuery.radiusSquared_value,factored,planar,normal,pack_eq,value,termValue,monomial,
      PolynomialOrder.value_add,PolynomialOrder.value_scale] <;> ring

theorem query_flops (x : Fin 3 → ℝ) (t : ℝ) :
    (PointingQuery.radiusFromDepth (x 2)).flops+(∑ i, (query x t i).flops)=25 := by
  rw [Fin.sum_univ_three]
  rfl

theorem physical_bound {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    (X : Motion (data.alpha:ℝ) (direction x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-(PointingCapFrame.reference (data.alpha:ℝ) t+
      PointingCapFrame.turn (data.alpha:ℝ) t
        (WithLp.toLp 2 (fun i => (query x t i).value)))‖≤(2968219/1000000000:ℝ) := by
  rw [query_matches hx]
  exact (PointingCapTimeData.ProfileTaylor4Time10Burn1200.prediction hx X t ht).1
end
end Quartic

/-- Both physical records meet the same position and velocity targets.
The printed fractions are upward-rounded proved bounds, not allowances. -/
theorem target_and_cost (x : Fin 3 → ℝ) (t : ℝ) :
    (1114279/125000000:ℚ)<1/100 ∧ (2968219/1000000000:ℚ)<1/100 ∧
    (53744171/1000000000000:ℚ)<1/10000 ∧ (2375577/125000000000:ℚ)<1/10000 ∧
    (∑ i, (Direct.query x t i).flops)=13 ∧
    (PointingQuery.radiusFromDepth (x 2)).flops+(∑ i, (Quartic.query x t i).flops)=25 :=
  ⟨by norm_num,by norm_num,by norm_num,by norm_num,Direct.query_flops x t,Quartic.query_flops x t⟩

theorem component_target_and_cost (x : Fin 3 → ℝ) (t : ℝ) :
    (2016289/1000000000:ℚ)<1/100 ∧ (16918551/1000000000000:ℚ)<1/10000 ∧
    (∑ i, (Component.query x t i).flops)=23 :=
  ⟨by norm_num,by norm_num,Component.query_flops x t⟩

end GNC.OrbitalComparison.PointingCapDirectComparison
