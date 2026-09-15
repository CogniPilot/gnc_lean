import GNC.Applications.OrbitalFuel.TransitionData.Block3

namespace GNC.Applications.OrbitalFuel.PolynomialTransition
open GNC.PolynomialODE GNC.PolynomialOrbitTransition

def steps : Fin 32 → BoxStep 25 := ![step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22, step23, step24, step25, step26, step27, step28, step29, step30, step31]

theorem steps_valid (j : Fin 32) : (steps j).Valid (field alpha) := by
  fin_cases j
  · exact step0_valid
  · exact step1_valid
  · exact step2_valid
  · exact step3_valid
  · exact step4_valid
  · exact step5_valid
  · exact step6_valid
  · exact step7_valid
  · exact step8_valid
  · exact step9_valid
  · exact step10_valid
  · exact step11_valid
  · exact step12_valid
  · exact step13_valid
  · exact step14_valid
  · exact step15_valid
  · exact step16_valid
  · exact step17_valid
  · exact step18_valid
  · exact step19_valid
  · exact step20_valid
  · exact step21_valid
  · exact step22_valid
  · exact step23_valid
  · exact step24_valid
  · exact step25_valid
  · exact step26_valid
  · exact step27_valid
  · exact step28_valid
  · exact step29_valid
  · exact step30_valid
  · exact step31_valid

theorem durations (j : Fin 32) : (steps j).duration = 3/160 := by
  fin_cases j <;> rfl

theorem joins (j : Fin 31) : (steps j.castSucc).Compatible (steps j.succ) := by
  fin_cases j
  · exact step1_join
  · exact step2_join
  · exact step3_join
  · exact step4_join
  · exact step5_join
  · exact step6_join
  · exact step7_join
  · exact step8_join
  · exact step9_join
  · exact step10_join
  · exact step11_join
  · exact step12_join
  · exact step13_join
  · exact step14_join
  · exact step15_join
  · exact step16_join
  · exact step17_join
  · exact step18_join
  · exact step19_join
  · exact step20_join
  · exact step21_join
  · exact step22_join
  · exact step23_join
  · exact step24_join
  · exact step25_join
  · exact step26_join
  · exact step27_join
  · exact step28_join
  · exact step29_join
  · exact step30_join
  · exact step31_join

theorem errors (j : Fin 32) (i : Fin 25) : (steps j).error i = error j.val i := by
  fin_cases j <;> rfl

theorem reference_error (j : Fin 32) (i : Fin 25) (hi : i.val < 5) :
    (steps j).error i < 1/10^19 := by
  rw [errors, error, if_pos hi]
  fin_cases j <;> norm_num

theorem transition_error (j : Fin 32) (i : Fin 25) (hi : 5 ≤ i.val) :
    (steps j).error i < 1/10^16 := by
  rw [errors, error, if_neg (by omega : ¬ i.val < 5)]
  fin_cases j <;> norm_num

end GNC.Applications.OrbitalFuel.PolynomialTransition
