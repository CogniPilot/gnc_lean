import GNC.Control.LogBackstepping

/-! A classical potential-based backstepping comparator.
The trace potential and a scaled half-angle potential are differentiated
from actual matrix kinematics. The comparison uses the same backstepping
mechanism; selecting logarithmic coordinates does not invent that mechanism.
-/
noncomputable section
open Matrix Real
namespace GNC.StandardBackstepping

def tracePotential (R : Cayley.Mat3) : ℝ := (3-R.trace)/2
def traceError (R : Cayley.Mat3) : Vec3 :=
  (1/2 : ℝ) • Cayley.unskew (R-Rᵀ)
def halfPotential (R : Cayley.Mat3) : ℝ := 4-2*sqrt (1+R.trace)
def halfError (R : Cayley.Mat3) : Vec3 :=
  (2/sqrt (1+R.trace)) • traceError R

theorem tracePotential_rotationExp (q : Vec3) :
    tracePotential (rotationExp q).val = 1-cos (enorm q) := by
  rw [tracePotential, rotationExp_trace]
  ring

theorem traceError_rotationExp (q : Vec3) :
    traceError (rotationExp q).val = (sin (enorm q)/enorm q) • q := by
  rw [traceError, rotationExp_antisymmetric]
  ext i
  fin_cases i <;> simp [Cayley.unskew, skew] <;> ring

theorem trace_derivative {R : ℝ → Cayley.Mat3} {w : Vec3} {t : ℝ}
    (hR : HasDerivAt R (R t*skew w) t) :
    HasDerivAt (fun s => (R s).trace) (-2*(traceError (R t) ⬝ᵥ w)) t := by
  have h0 := hasDerivAt_pi.mp (hasDerivAt_pi.mp hR (0 : Fin 3)) (0 : Fin 3)
  have h1 := hasDerivAt_pi.mp (hasDerivAt_pi.mp hR (1 : Fin 3)) (1 : Fin 3)
  have h2 := hasDerivAt_pi.mp (hasDerivAt_pi.mp hR (2 : Fin 3)) (2 : Fin 3)
  convert (h0.add h1).add h2 using 1
  · ext s; simp [Matrix.trace, Fin.sum_univ_succ, add_assoc]
  · simp [traceError, Cayley.unskew, skew, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ]
    ring

theorem tracePotential_derivative {R : ℝ → Cayley.Mat3} {w : Vec3} {t : ℝ}
    (hR : HasDerivAt R (R t*skew w) t) :
    HasDerivAt (fun s => tracePotential (R s)) (traceError (R t) ⬝ᵥ w) t := by
  convert ((trace_derivative hR).const_sub 3).div_const 2 using 1
  ring

theorem halfPotential_derivative {R : ℝ → Cayley.Mat3} {w : Vec3} {t : ℝ}
    (hR : HasDerivAt R (R t*skew w) t) (ht : 0 < 1+(R t).trace) :
    HasDerivAt (fun s => halfPotential (R s)) (halfError (R t) ⬝ᵥ w) t := by
  have h := (((trace_derivative hR).const_add 1).sqrt ht.ne').const_mul 2
  convert h.const_sub 4 using 1
  simp [halfError, smul_dotProduct]
  ring

/-- Classical backstepping cancellation for any configuration potential
with its actual power pairing. This includes trace, half-angle and log
potentials; it is not a special invention of the logarithmic controller. -/
theorem potential_energy_derivative {Ψ : ℝ → ℝ} {z : ℝ → Vec3}
    {e : Vec3} {kq kz t : ℝ}
    (hΨ : HasDerivAt Ψ (e ⬝ᵥ (-kq • e+z t)) t)
    (hz : HasDerivAt z (-kz • z t-e) t) :
    HasDerivAt (fun s => Ψ s+lengthSq (z s)/2)
      (-kq*lengthSq e-kz*lengthSq (z t)) t := by
  convert hΨ.add ((LogBackstepping.lengthSq_derivative hz).div_const 2) using 1
  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    dot_self_lengthSq, dotProduct_comm (z t) e]
  ring

end GNC.StandardBackstepping
