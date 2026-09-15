import GNC.Applications.OrbitalFuel.FixedRollCertificate

/-! The six commanded attitudes and the roll reversal are actual SO(3)
elements. This checks the geometry; continuous slew realization and its
power/propellant costs are separate physical obligations. -/
noncomputable section
open Matrix GNC GNC.SharedBias GNC.FuelCertificate
open scoped Matrix
namespace GNC.Applications.OrbitalFuel.SharedBiasGeometry
open SharedBiasExample (axis)

def base : Fin 6 → Matrix (Fin 3) (Fin 3) ℝ :=
  ![!![0,0,1; 1,0,0; 0,1,0], !![1,0,0; 0,0,1; 0,-1,0],
    !![1,0,0; 0,1,0; 0,0,1], !![0,0,-1; 1,0,0; 0,-1,0],
    !![1,0,0; 0,0,-1; 0,1,0], !![1,0,0; 0,-1,0; 0,0,-1]]

def reversal : Matrix (Fin 3) (Fin 3) ℝ := !![-1,0,0; 0,-1,0; 0,0,1]
def direction : Fin 6 → Vec3 :=
  ![![1,0,0], ![0,1,0], ![0,0,1], ![-1,0,0], ![0,-1,0], ![0,0,-1]]

theorem base_orthogonal (i : Fin 6) : (base i).transpose * base i = 1 := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [base, mul_apply, Fin.sum_univ_succ]

theorem base_det (i : Fin 6) : (base i).det = 1 := by
  fin_cases i <;> norm_num [base, det_fin_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]

def baseRotation (i : Fin 6) : SO3 :=
  ⟨base i, (mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr (base_orthogonal i), base_det i⟩

def rollReversal : SO3 := by
  refine ⟨reversal, ?_, ?_⟩
  · apply (mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr
    ext r c
    fin_cases r <;> fin_cases c <;> norm_num [reversal, mul_apply, Fin.sum_univ_succ]
  · norm_num [reversal, det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem base_direction (i : Fin 6) : rotate (baseRotation i) axis = direction i := by
  fin_cases i <;> ext r <;> fin_cases r <;>
    norm_num [rotate, baseRotation, base, axis, direction, mulVec, dotProduct, Fin.sum_univ_succ]

theorem reversal_nominal : rotate rollReversal axis = axis := by
  ext r
  fin_cases r <;>
    norm_num [rotate, rollReversal, reversal, axis, mulVec, dotProduct, Fin.sum_univ_succ]

def cycleRotation (j : Fin 18) : SO3 :=
  baseRotation ⟨j.val % 6, Nat.mod_lt _ (by norm_num)⟩ *
    if j.val / 6 % 2 = 1 then rollReversal else 1

theorem cycle_direction (j : Fin 18) : rotate (cycleRotation j) axis =
    direction ⟨j.val % 6, Nat.mod_lt _ (by norm_num)⟩ := by
  dsimp [cycleRotation]
  rw [rotate_mul]
  split_ifs
  · rw [reversal_nominal, base_direction]
  · simpa [rotate] using base_direction ⟨j.val % 6, Nat.mod_lt _ (by norm_num)⟩

theorem reversal_action (v : Vec3) : reversal *ᵥ v =
    fun k => if k.val < 2 then -v k else v k := by
  ext k
  fin_cases k <;> norm_num [reversal, mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals rfl

/-- Exact rational thresholds reported in the manuscript, using the already
checked upper costs and necessary-cut lower bounds. -/
theorem earth_gap :
    33507/10000000 < boxLower SharedBiasCertificates.Earth.A SharedBiasCertificates.Earth.b
      SharedBiasCertificates.Earth.c SharedBiasCertificates.Earth.dual -
      Cost SharedBiasCertificates.Earth.c SharedBiasCertificates.Earth.x := by
  rw [SharedBiasCertificates.Earth.lower_value, SharedBiasCertificates.Earth.cost_value]
  norm_num

theorem solar_gap :
    15228/100000 < boxLower SharedBiasCertificates.Solar.A SharedBiasCertificates.Solar.b
      SharedBiasCertificates.Solar.c SharedBiasCertificates.Solar.dual -
      Cost SharedBiasCertificates.Solar.c SharedBiasCertificates.Solar.x := by
  rw [SharedBiasCertificates.Solar.lower_value, SharedBiasCertificates.Solar.cost_value]
  norm_num

theorem roll_gap :
    23663/10000000 < boxLower FixedRollCertificate.cut SharedBiasCertificates.Earth.b
      SharedBiasCertificates.Earth.c FixedRollCertificate.multiplier -
      Cost SharedBiasCertificates.Earth.c SharedBiasCertificates.Earth.x := by
  rw [FixedRollCertificate.lower_value, SharedBiasCertificates.Earth.cost_value]
  norm_num

end GNC.Applications.OrbitalFuel.SharedBiasGeometry
