import GNC.Applications.OrbitalFuel.FreeResponseFormula
import GNC.Applications.OrbitalFuel.SharedBiasCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace GNC.Applications.OrbitalFuel.FreeResponse

def reported : Fin 6 → ℚ := ![(-837719698489/250000000000), (-151155186038243/2000000000000), (2260523467411/500000000000), (2064284120987/80000000000), (-17213728086893/2000000000000), (-783089374771/400000000000)]

def negativeRow (i : Fin 6) : Fin 12 := ⟨2*i.val,by omega⟩
def positiveRow (i : Fin 6) : Fin 12 := ⟨2*i.val+1,by omega⟩

theorem reported_matches (i : Fin 6) : (reported i:ℝ) =
    (SharedBiasCertificates.Solar.b (negativeRow i)-SharedBiasCertificates.Solar.b (positiveRow i))/2 := by
  fin_cases i <;> norm_num [reported, negativeRow, positiveRow, SharedBiasCertificates.Solar.b,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem output_certificate : ∀ i,
    (constraintOutput i).differenceMajorant region allowance+
      |(constraintOutput i).ratValue center-reported i| ≤ 1/10^10 := by decide +kernel

end GNC.Applications.OrbitalFuel.FreeResponse
