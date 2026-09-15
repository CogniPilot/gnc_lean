import GNC.Magnus.ClosedExponential
import GNC.Magnus.MagnusFlow
import GNC.Dynamics.MatrixDynamics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact nilpotent gravity-side factor in the mixed spacecraft equation.
The supplied gravity history may be gravity along the actual trajectory.
Its two moments then remain unknown: matrix Magnus termination does not
solve the nonlinear orbit. All exponent and ODE equalities below are exact.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.GravityFactor
open Matrix MeasureTheory
open scoped Matrix.Norms.Operator

def generator (g : Vec3) : Mat5 := Magnus.ideal 0 g (-1)
def input (a w : Vec3) : Mat5 := Magnus.extended ![0,a,w] 1

theorem spacecraft_split (X : SE23) (g a w : Vec3) :
    spacecraftDerivative X ![0,a,w] g =
      generator g*SE23.toMatrix X+SE23.toMatrix X*input a w := by
  simp only [spacecraftDerivative, generator, input, Magnus.ideal, Magnus.extended,
    velocityOnly, neg_one_smul, one_smul, sub_eq_add_neg]

theorem generator_commutator (g h : Vec3) :
    generator g*generator h-generator h*generator g = Magnus.ideal (h-g) 0 0 := by
  rw [generator, generator, Magnus.ideal_commutator]
  simp only [neg_one_smul, sub_neg_eq_add]
  congr 1
  abel

/-- Every nested bracket of length at least three vanishes in this factor.
No state-independence assumption on the sampled vectors is used. -/
theorem generator_triple (g h k : Vec3) :
    generator g*(generator h*generator k-generator k*generator h)-
      (generator h*generator k-generator k*generator h)*generator g = 0 :=
  Magnus.ideal_triple_commutator 0 g 0 h 0 k (-1) (-1) (-1)

def zeroth (g : ℝ → Vec3) (t : ℝ) : Vec3 := ∫ s in (0:ℝ)..t, g s
def first (g : ℝ → Vec3) (t : ℝ) : Vec3 := ∫ s in (0:ℝ)..t, s • g s

def exponent (g : ℝ → Vec3) (t : ℝ) : Mat5 :=
  Magnus.ideal ((t/2) • zeroth g t-first g t) (zeroth g t) (-t)

def factor (g : ℝ → Vec3) (t : ℝ) : Mat5 :=
  1+Magnus.ideal (-first g t) (zeroth g t) (-t)

theorem factor_exponential (g : ℝ → Vec3) (t : ℝ) :
    NormedSpace.exp (exponent g t) = factor g t := by
  have he := Magnus.exp_extended_zero
    ![(t/2) • zeroth g t-first g t,zeroth g t,0] (-t) 1 rfl
  simp only [one_smul, one_pow, Magnus.ideal, exponent] at he ⊢
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [factor, Magnus.ideal, Magnus.extended, hat, kinematicC,
      pow_two, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private def lift : (LogState × ℝ) →L[ℝ] Mat5 :=
  { Magnus.extendedLinear with cont := Magnus.extendedLinear.continuous_of_finiteDimensional }

private theorem ideal_derivative {p v : ℝ → Vec3} {b : ℝ → ℝ}
    {dp dv : Vec3} {db t : ℝ}
    (hp : HasDerivAt p dp t) (hv : HasDerivAt v dv t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun s => Magnus.ideal (p s) (v s) (b s))
      (Magnus.ideal dp dv db) t := by
  have hx : HasDerivAt (fun s => (![p s,v s,0] : LogState)) ![dp,dv,0] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hp
    · exact hv
    · exact hasDerivAt_const t 0
  exact lift.hasFDerivAt.comp_hasDerivAt t (hx.prodMk hb)

theorem zeroth_derivative (g : ℝ → Vec3) (hg : Continuous g) (t : ℝ) :
    HasDerivAt (zeroth g) (g t) t :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

theorem first_derivative (g : ℝ → Vec3) (hg : Continuous g) (t : ℝ) :
    HasDerivAt (first g) (t • g t) t := by
  have hc : Continuous (fun s : ℝ => s • g s) := continuous_id.smul hg
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem factor_initial (g : ℝ → Vec3) : factor g 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [factor, first, zeroth, Magnus.ideal, Magnus.extended, hat, kinematicC]

theorem factor_derivative (g : ℝ → Vec3) (hg : Continuous g) (t : ℝ) :
    HasDerivAt (factor g) (generator (g t)*factor g t) t := by
  have hd := (ideal_derivative (first_derivative g hg t).neg
    (zeroth_derivative g hg t) (hasDerivAt_id t).neg).const_add (1 : Mat5)
  convert hd using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, factor, Magnus.ideal, Magnus.extended, hat, kinematicC,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> norm_num <;> ring

/-- The exact, terminating left-Magnus differential equation. The double
adjoint is zero. This is stronger than merely observing a finite matrix
power relation at one time. -/
theorem exponent_derivative (g : ℝ → Vec3) (hg : Continuous g) (t : ℝ) :
    HasDerivAt (exponent g)
      (generator (g t)-(1/2:ℝ) •
        (exponent g t*generator (g t)-generator (g t)*exponent g t)) t := by
  have hp := ((((hasDerivAt_id t).div_const 2).smul
    (zeroth_derivative g hg t)).sub (first_derivative g hg t))
  have hd := ideal_derivative hp (zeroth_derivative g hg t) (hasDerivAt_id t).neg
  convert hd using 1
  rw [exponent, generator, Magnus.ideal_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Magnus.ideal, Magnus.extended, hat, kinematicC] <;> ring

/-- Once a right input flow has been obtained, these two gravity moments
give the exact mixed solution for the supplied gravity history. Substituting
g(p(t)) makes this a conditional identity, not a closed nonlinear solver. -/
theorem mixed_derivative (g : ℝ → Vec3) (hg : Continuous g)
    {U N : ℝ → Mat5} (X₀ : Mat5)
    (hU : ∀ t, HasDerivAt U (U t*N t) t) (t : ℝ) :
    HasDerivAt (fun s => factor g s*X₀*U s)
      (generator (g t)*(factor g t*X₀*U t)+(factor g t*X₀*U t)*N t) t :=
  Magnus.factor_derivative (factor_derivative g hg t) (hU t)

end GNC.GravityFactor
