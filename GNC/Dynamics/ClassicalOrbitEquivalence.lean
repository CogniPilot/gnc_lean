import GNC.Dynamics.RadialGravityFrame
import GNC.Magnus.NilpotentInteraction

/-! Exact equivalence of the retained translational variational equations.
The velocity in `logGenerator` is rotated inertial velocity, whereas the
classical velocity is the time derivative of rotating position. The Euler
term is essential on eccentric orbits. These are statements about the
linearized equations, not finite-separation nonlinear Kepler motion. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
namespace GNC.ClassicalOrbitEquivalence
open RotatingVariational RadialGravityFrame
abbrev M6 := Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ

def inverseDerivative (Wdot : M3) : M6 := fromBlocks 0 0 Wdot 0

theorem inverse_derivative (W : ℝ → M3) {Wdot : M3} {t : ℝ}
    (hW : HasDerivAt W Wdot t) :
    HasDerivAt (fun s => coordinateInverse (W s)) (inverseDerivative Wdot) t := by
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  rcases i with i | i <;> rcases j with j | j
  · exact hasDerivAt_const t ((1 : M3) i j)
  · exact hasDerivAt_const t 0
  · exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hW i) j
  · exact hasDerivAt_const t ((1 : M3) i j)

theorem inverse_connection (G W Wdot : M3) :
    inverseDerivative Wdot + coordinateInverse W * classicalGenerator G W Wdot =
      logGenerator G W * coordinateInverse W := by
  simp only [inverseDerivative, coordinateInverse, logGenerator, classicalGenerator,
    fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, fromBlocks_add]
  congr 1 <;> simp [two_smul, add_mul, mul_neg, neg_mul] <;> abel

/-- Transport every solution column, including all six fundamental columns. -/
theorem to_classical {W : ℝ → M3} {F : ℝ → M6} {G Wdot : M3} {t : ℝ}
    (hW : HasDerivAt W Wdot t)
    (hF : HasDerivAt F (logGenerator G (W t) * F t) t) :
    HasDerivAt (fun s => coordinateChange (W s) * F s)
      (classicalGenerator G (W t) Wdot * (coordinateChange (W t) * F t)) t := by
  convert (coordinate_derivative W hW).mul hF using 1
  simp only [← mul_assoc]
  rw [← add_mul, connection]

theorem to_log {W : ℝ → M3} {F : ℝ → M6} {G Wdot : M3} {t : ℝ}
    (hW : HasDerivAt W Wdot t)
    (hF : HasDerivAt F (classicalGenerator G (W t) Wdot * F t) t) :
    HasDerivAt (fun s => coordinateInverse (W s) * F s)
      (logGenerator G (W t) * (coordinateInverse (W t) * F t)) t := by
  convert (inverse_derivative W hW).mul hF using 1
  simp only [← mul_assoc]
  rw [← add_mul, inverse_connection]

/-- Both implications; no assumed differentiability of F is needed in advance. -/
theorem solution_iff {W : ℝ → M3} {F : ℝ → M6} {G Wdot : M3} {t : ℝ}
    (hW : HasDerivAt W Wdot t) :
    HasDerivAt F (logGenerator G (W t) * F t) t ↔
    HasDerivAt (fun s => coordinateChange (W s) * F s)
      (classicalGenerator G (W t) Wdot * (coordinateChange (W t) * F t)) t := by
  constructor
  · exact to_classical hW
  · intro h
    simpa only [← mul_assoc, cancel', Matrix.one_mul] using to_log hW h

def transport (W : ℝ → M3) (F : ℝ → M6) (s t : ℝ) : M6 :=
  coordinateChange (W t) * F t * coordinateInverse (W s)

theorem transport_initial (W : ℝ → M3) (F : ℝ → M6) (s : ℝ) (hF : F s = 1) :
    transport W F s s = 1 := by simp [transport, hF]

/-- The STM uses coordinate conversion at BOTH endpoints. -/
theorem transport_derivative {W : ℝ → M3} {F : ℝ → M6} {G Wdot : M3} {s t : ℝ}
    (hW : HasDerivAt W Wdot t)
    (hF : HasDerivAt F (logGenerator G (W t) * F t) t) :
    HasDerivAt (transport W F s)
      (classicalGenerator G (W t) Wdot * transport W F s t) t := by
  unfold transport
  simpa only [mul_assoc] using (to_classical hW hF).mul_const
    (coordinateInverse (W s))

def hcw (n : ℝ) : M6 :=
  fromBlocks 0 1 (diagonal ![3*n^2,0,-n^2])
    !![0,2*n,0; -2*n,0,0; 0,0,0]

/-- The circular Kepler relation and zero frame acceleration give HCW. -/
theorem hcw_generator {μ r n : ℝ} (hKepler : μ/r^3 = n^2) :
    classicalGenerator (gravity (μ/r^3)) (omega n) (omega 0) = hcw n := by
  rw [hKepler, classical_blocks]
  unfold hcw
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal] <;> ring

def th (k : ℝ) : M6 :=
  fromBlocks 0 1 (diagonal ![3/k,0,-1]) (-(2:ℝ) • omega 1)

/-- Circular true-anomaly TH is unit-frequency HCW. -/
theorem th_circular : th 1 = hcw 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> norm_num [th, hcw, diagonal, omega, skew, Matrix.cons_val_two]

/-- `k = 1 + e cos ν`, `kp = dk/dν`, `w = dν/dt`.
This maps (rotating position, its time derivative) to (k x, d(k x)/dν). -/
def anomalyChange (k kp w : ℝ) : M6 :=
  fromBlocks (k • (1:M3)) 0 (kp • (1:M3)) ((k/w) • (1:M3))

def anomalyInverse (k kp w : ℝ) : M6 :=
  fromBlocks ((1/k) • (1:M3)) 0 ((-kp*w/k^2) • (1:M3)) ((w/k) • (1:M3))

def anomalyDerivative (k kp w : ℝ) : M6 :=
  fromBlocks ((w*kp) • (1:M3)) 0 ((w*(1-k)) • (1:M3)) (-kp • (1:M3))

theorem anomaly_cancel {k w : ℝ} (hk : k ≠ 0) (hw : w ≠ 0) (kp : ℝ) :
    anomalyChange k kp w * anomalyInverse k kp w = 1 ∧
    anomalyInverse k kp w * anomalyChange k kp w = 1 := by
  constructor <;> ext i j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [anomalyChange, anomalyInverse, fromBlocks_multiply, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply, hk, hw] <;> field_simp <;> ring

/-- Kepler identities c=w²/k and wdot=2 w² kp/k yield the canonical TH ODE:
u₁''=3u₁/k+2u₂', u₂''=-2u₁', u₃''=-u₃, with primes in true anomaly. -/
theorem anomaly_connection {k w : ℝ} (hk : k ≠ 0) (hw : w ≠ 0) (kp : ℝ) :
    anomalyDerivative k kp w + anomalyChange k kp w *
      classicalGenerator (gravity (w^2/k)) (omega w) (omega (2*w^2*kp/k)) =
      (w • th k) * anomalyChange k kp w := by
  rw [classical_blocks]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [anomalyDerivative, anomalyChange, th, fromBlocks_multiply,
      Matrix.mul_apply, Fin.sum_univ_succ, diagonal, omega, skew,
      Matrix.cons_val_two, Matrix.one_apply] <;> field_simp <;> ring

theorem anomaly_derivative {k kp w : ℝ → ℝ} {t : ℝ}
    (hk : k t ≠ 0) (hw : w t ≠ 0)
    (hkd : HasDerivAt k (w t * kp t) t)
    (hkpd : HasDerivAt kp (w t * (1-k t)) t)
    (hwd : HasDerivAt w (2*(w t)^2*kp t/k t) t) :
    HasDerivAt (fun s => anomalyChange (k s) (kp s) (w s))
      (anomalyDerivative (k t) (kp t) (w t)) t := by
  have hquot : HasDerivAt (fun s => k s/w s) (-kp t) t := by
    convert hkd.div hwd hw using 1
    field_simp
    ring
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  rcases i with i | i <;> rcases j with j | j
  · exact hkd.mul_const ((1:M3) i j)
  · exact hasDerivAt_const t 0
  · exact hkpd.mul_const ((1:M3) i j)
  · exact hquot.mul_const ((1:M3) i j)

/-- Physical-time form of the true-anomaly TH solution, with the clock
factor retained. Reparameterizing by ν gives the standard TH equation. -/
theorem to_th {k kp w : ℝ → ℝ} {F : ℝ → M6} {t : ℝ}
    (hk : k t ≠ 0) (hw : w t ≠ 0)
    (hkd : HasDerivAt k (w t * kp t) t)
    (hkpd : HasDerivAt kp (w t * (1-k t)) t)
    (hwd : HasDerivAt w (2*(w t)^2*kp t/k t) t)
    (hF : HasDerivAt F
      (classicalGenerator (gravity ((w t)^2/k t)) (omega (w t))
        (omega (2*(w t)^2*kp t/k t)) * F t) t) :
    HasDerivAt (fun s => anomalyChange (k s) (kp s) (w s) * F s)
      ((w t • th (k t)) * (anomalyChange (k t) (kp t) (w t) * F t)) t := by
  convert (anomaly_derivative hk hw hkd hkpd hwd).mul hF using 1
  simp only [← mul_assoc]
  rw [← add_mul, anomaly_connection hk hw]

end GNC.ClassicalOrbitEquivalence
