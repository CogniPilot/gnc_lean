import GNC.Applications.OrbitalComparison.PointingCapFrame

/-! A complete physical defect for quadratic pointing responses, including
both the cubic gravity remainder and the first/second-response difference. -/
noncomputable section
namespace GNC.OrbitalComparison.PointingCapDefect
open PointingCapFrame SpatialBurn UniformCertificate

def residual (α : ℝ) (d v a y f : E3) : E3 :=
  a-positionOperator α d-velocityOperator α v-f-quadratic α y

theorem physical_defect_identity (α t : ℝ) (n : E3) (d v a y : ℝ → E3) (f : E3) :
    acceleration α d v a t-physicalAcceleration α n t (position α d t) =
      turn α t (residual α (d t) (v t) (a t) (y t) f)-
        scale α • Gravity.quadraticResidual mu (reference α t) (turn α t (d t)) (turn α t (y t))+
        turn α t (f-(scale α*(Direct.thrust:ℝ)) • (n-e0)) := by
  rw [residual,map_sub,← linear_residual_identity,← physical_quadratic]
  dsimp [acceleration,physicalAcceleration,position,Gravity.quadraticResidual]
  simp only [map_sub,map_smul]
  module

theorem physical_defect_bound (α t : ℝ) (n : E3) (d v a y : ℝ → E3) (f : E3)
    {P Y E L S : ℝ} (hP : P<7000000) (hd : ‖d t‖≤P) (hy : ‖y t‖≤Y)
    (hdy : ‖d t-y t‖≤E) (hL : ‖residual α (d t) (v t) (a t) (y t) f‖≤L)
    (hS : ‖f-(scale α*(Direct.thrust:ℝ)) • (n-e0)‖≤S) :
    ‖physicalAcceleration α n t (position α d t)-acceleration α d v a t‖≤
      L+S+scale α*((3*mu/7000000^4)*E*(P+Y)+(4*mu/(7000000-P)^5)*P^3) := by
  have hs : 0≤scale α := by unfold scale; positivity
  have hg := Gravity.quadratic_residual_bound mu (by norm_num [mu])
    (reference α t) (turn α t (d t)) (turn α t (y t)) (D := P) hP
    (by rw [reference_norm]) (by simpa only [turn_norm] using hd) le_rfl
    (by simpa only [turn_norm] using hy) (by simpa only [← map_sub,turn_norm] using hdy)
  have hgs := mul_le_mul_of_nonneg_left hg hs
  rw [norm_sub_rev,physical_defect_identity α t n d v a y f]
  have hscaled : ‖scale α • Gravity.quadraticResidual mu (reference α t)
      (turn α t (d t)) (turn α t (y t))‖≤
      scale α*((3*mu/7000000^4)*E*(P+Y)+(4*mu/(7000000-P)^5)*P^3) := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs] using hgs
  have ht := norm_sub_le (turn α t (residual α (d t) (v t) (a t) (y t) f))
    (scale α • Gravity.quadraticResidual mu (reference α t) (turn α t (d t)) (turn α t (y t)))
  rw [turn_norm] at ht
  have hsour : ‖turn α t (f-(scale α*(Direct.thrust:ℝ)) • (n-e0))‖≤S := by
    simpa only [turn_norm] using hS
  exact (norm_add_le _ _).trans (by linarith)

end GNC.OrbitalComparison.PointingCapDefect
