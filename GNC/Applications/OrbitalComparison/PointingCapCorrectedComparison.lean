import GNC.Applications.OrbitalComparison.PointingCapDirectComparison
import GNC.Applications.OrbitalComparison.PointingCapTimeData.PrefixDirectTime11Burn1200
import GNC.Applications.OrbitalComparison.PointingCapTimeData.PrefixProfileComponentTime10Burn1200
import GNC.Applications.OrbitalComparison.PointingCapTimeData.PrefixProfileTaylor4Time10Burn1200
import GNC.Applications.OrbitalComparison.PointingCapTimeData.MixedCorrectionTime11Degree8Burn1200

/-! A checked mixed-term correction and its actual nineteen-operation query.
The companion generation graph has an empirical count of 201 operations;
that count and floating-point execution are outside the theorems here. -/
namespace GNC.OrbitalComparison.PointingCapCorrectedComparison
open ParameterPolynomial PointingCapCertificate PointingCapBurn SpatialBurn Set
open PointingCapDirectComparison (curve)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev data := PointingCapData.MixedCorrectionTime11Degree8Burn1200.data
def planar (i : Fin 3) : Coefficients :=
  [⟨1,0,0,curve data i 1 0 0⟩,⟨0,0,1,curve data i 0 0 1⟩,
   ⟨2,0,0,curve data i 2 0 0⟩,⟨1,0,1,curve data i 1 0 1⟩]
def normal : Coefficients :=
  [⟨0,1,0,curve data 2 0 1 0⟩,⟨1,1,0,curve data 2 1 1 0⟩,⟨0,1,1,curve data 2 0 1 1⟩]
def factored : PointingCapPolynomial.Vector := ![planar 0,planar 1,normal]
theorem factorization : ∀ i, zero (subtract (data.q i) (factored i)) := by decide +kernel

noncomputable section
def coefficient (i : Fin 3) (u v c : ℕ) (t : ℝ) :=
  PolynomialOrder.value (curve data i u v c) t
def queryPlanar (i : Fin 3) (u c t : ℝ) : Planning.FlopKernel.Value ℝ :=
  let L := coefficient i 1 0 0 t
  let Q := coefficient i 2 0 0 t
  let D := coefficient i 1 0 1 t
  let C := coefficient i 0 0 1 t
  Planning.FlopKernel.add
    (Planning.FlopKernel.mul (Planning.FlopKernel.input u)
      (Planning.FlopKernel.add
        (Planning.FlopKernel.add (Planning.FlopKernel.input L)
          (Planning.FlopKernel.mul (Planning.FlopKernel.input u) (Planning.FlopKernel.input Q)))
        (Planning.FlopKernel.mul (Planning.FlopKernel.input c) (Planning.FlopKernel.input D))))
    (Planning.FlopKernel.mul (Planning.FlopKernel.input c) (Planning.FlopKernel.input C))
def query (x : Fin 3 → ℝ) (t : ℝ) : Fin 3 → Planning.FlopKernel.Value ℝ :=
  ![queryPlanar 0 (x 0) (x 2) t,queryPlanar 1 (x 0) (x 2) t,
    PointingQuery.normal (x 0) (x 1) (x 2)
      (coefficient 2 0 1 0 t) (coefficient 2 1 1 0 t) (coefficient 2 0 1 1 t)]

theorem query_matches (x : Fin 3 → ℝ) (t : ℝ) :
    WithLp.toLp 2 (fun i => (query x t i).value)=data.displacement x t := by
  have h (i : Fin 3) := ParameterPolynomial.identity _ _ (factorization i) x t
  simp only [Data.displacement,PointingCapPolynomial.vectorValue,h]
  ext i
  fin_cases i <;>
    simp [query,queryPlanar,coefficient,PointingQuery.normal_value,
      Planning.FlopKernel.add,Planning.FlopKernel.mul,Planning.FlopKernel.input,
      factored,planar,normal,pack_eq,value,termValue,monomial] <;> ring

theorem query_flops (x : Fin 3 → ℝ) (t : ℝ) : (∑ i, (query x t i).flops)=19 := by
  rw [Fin.sum_univ_three]
  rfl

theorem physical_bound {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    (X : Motion (data.alpha:ℝ) (direction x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-(PointingCapFrame.reference (data.alpha:ℝ) t+
      PointingCapFrame.turn (data.alpha:ℝ) t
        (WithLp.toLp 2 (fun i => (query x t i).value)))‖≤(1340259/1000000000:ℝ) := by
  rw [query_matches]
  exact (PointingCapTimeData.MixedCorrectionTime11Degree8Burn1200.prediction hx X t ht).1

/-- Strictly tighter reported bounds with a cheaper exact query. This does
not compare actual errors or prove a globally optimal coefficient generator. -/
theorem bound_and_query_improvement (x : Fin 3 → ℝ) (t : ℝ) :
    (1340259/1000000000:ℚ)<201627/100000000 ∧
    (9834489/1000000000000:ℚ)<8459057/500000000000 ∧
    (∑ i, (query x t i).flops)<(∑ i, (PointingCapDirectComparison.Component.query x t i).flops) := by
  rw [query_flops,PointingCapDirectComparison.Component.query_flops]
  norm_num

end
end GNC.OrbitalComparison.PointingCapCorrectedComparison
