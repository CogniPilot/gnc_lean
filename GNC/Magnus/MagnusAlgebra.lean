import GNC.Lie.SE23
import GNC.Analysis.MixedFlow

/-! The time-extended algebra, commutator, and exact mixed-flow splitting
in main.pdf. Coordinate order remains (position, velocity, rotation). -/
noncomputable section
namespace GNC.Magnus
set_option maxHeartbeats 1500000
open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator

def extended (x : LogState) (β : ℝ) : Mat5 := hat x + β • kinematicC

def extendedBracket (x y : LogState) (β γ : ℝ) : LogState :=
  ad x y + ![γ • x 1 - β • y 1, 0, 0]

/-- Proposition 2 / Eq. (14), including the sign of the time corner. -/
theorem extended_commutator (x y : LogState) (β γ : ℝ) :
    extended x β * extended y γ - extended y γ * extended x β =
      extended (extendedBracket x y β γ) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [extended, extendedBracket, hat, kinematicC, ad, crossProduct,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

def ideal (p v : Vec3) (β : ℝ) : Mat5 := extended ![p,v,0] β

/-- Brackets in the translation/time ideal occupy only the position column. -/
theorem ideal_commutator (p v q w : Vec3) (β γ : ℝ) :
    ideal p v β * ideal q w γ - ideal q w γ * ideal p v β =
      ideal (γ • v - β • w) 0 0 := by
  rw [ideal, ideal, extended_commutator]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [extendedBracket, ad, crossProduct, ideal]

/-- Proposition 2: the translation/time ideal is two-step nilpotent. -/
theorem ideal_triple_commutator (p v q w r u : Vec3) (β γ δ : ℝ) :
    ideal p v β * (ideal q w γ * ideal r u δ - ideal r u δ * ideal q w γ) -
      (ideal q w γ * ideal r u δ - ideal r u δ * ideal q w γ) * ideal p v β = 0 := by
  rw [ideal_commutator, ideal_commutator]
  ext i j; fin_cases i <;> fin_cases j <;> simp [ideal, extended, hat]

/-- Eq. (15): the three components of one FOH commutator. Slopes rather
than sample differences remove an artificial division by the step size. -/
theorem foh_commutator (ω a dω da : Vec3) :
    extended ![0,a,ω] 1 * extended ![0,da,dω] 0 -
      extended ![0,da,dω] 0 * extended ![0,a,ω] 1 =
      extended ![-da, crossProduct ω da - crossProduct dω a,
        crossProduct ω dω] 0 := by
  rw [extended_commutator]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [extendedBracket, ad, crossProduct] <;> ring

section Flow
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Exact factorization works also for time-varying left generators; it does
not require existence or convergence of a single global Magnus logarithm. -/
theorem factor_derivative {L R : ℝ → A} {M N X₀ : A} {t : ℝ}
    (hL : HasDerivAt L (M * L t) t) (hR : HasDerivAt R (R t * N) t) :
    HasDerivAt (fun s => L s * X₀ * R s)
      (M * (L t * X₀ * R t) + (L t * X₀ * R t) * N) t := by
  convert (hL.mul_const X₀).mul hR using 1 <;> noncomm_ring

/-- Lemma 4's change of variables, stated directly for the flow. -/
theorem peel_left {X : ℝ → A} {M N : A} {t : ℝ}
    (hX : HasDerivAt X (M * X t + X t * N) t) :
    HasDerivAt (fun s => exp ((-s) • M) * X s)
      ((exp ((-t) • M) * X t) * N) t := by
  have hL := (hasDerivAt_exp_smul_const M (-t)).scomp t (hasDerivAt_id t).neg
  convert hL.mul hX using 1
  simp only [Function.comp_apply, neg_one_smul]
  noncomm_ring

/-- Theorem 6: exact transport of a finite correction by any invertible
buffered right factor, independent of the initial state. -/
theorem reapplication (L X D : A) (R : Aˣ) :
    L * (X * D) * (R : A) = (L * X * (R : A)) * ((↑R⁻¹ : A) * D * R) := by
  simp only [mul_assoc]
  rw [show (R : A) * ((↑R⁻¹ : A) * (D * R)) = D * R by
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]]

end Flow
end GNC.Magnus
