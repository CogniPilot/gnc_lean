import GNC.Magnus.GravityFactor

/-! Explicit input-side commutators for arbitrary angular velocity and body
thrust acceleration. These are matrix integrands, not a convergence theorem.
Right evolution U'=UN reverses the sign of the second Magnus term relative
to left evolution; the displayed commutator itself always means XY-YX.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.InputMagnus
open Matrix
open GravityFactor

def pairCoordinates (a w b z : Vec3) : LogState :=
  ![a-b,w ⨯₃ b-z ⨯₃ a,w ⨯₃ z]

theorem input_commutator (a w b z : Vec3) :
    input a w*input b z-input b z*input a w =
      Magnus.extended (pairCoordinates a w b z) 0 := by
  rw [input, input, Magnus.extended_commutator]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Magnus.extendedBracket, pairCoordinates, ad, crossProduct] <;> ring

/-- Explicit recursion for every further bracket with a sampled input.
This includes the position term from the time corner, which cannot be
dropped when computing coning/sculling/scrolling or higher Magnus terms. -/
theorem bracket_with_coordinates (a w : Vec3) (x : LogState) :
    input a w*Magnus.extended x 0-Magnus.extended x 0*input a w =
      Magnus.extended ![w ⨯₃ x 0-x 1,w ⨯₃ x 1-x 2 ⨯₃ a,w ⨯₃ x 2] 0 := by
  rw [input, Magnus.extended_commutator]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Magnus.extendedBracket, ad, crossProduct, vecHead, vecTail] <;> ring

theorem input_triple (a w b z c y : Vec3) :
    input a w*(input b z*input c y-input c y*input b z)-
      (input b z*input c y-input c y*input b z)*input a w =
      Magnus.extended
        ![w ⨯₃ (b-c)-(z ⨯₃ c-y ⨯₃ b),
          w ⨯₃ (z ⨯₃ c-y ⨯₃ b)-(z ⨯₃ y) ⨯₃ a,w ⨯₃ (z ⨯₃ y)] 0 := by
  rw [input_commutator, bracket_with_coordinates]
  rfl

/-- With no angular velocity, arbitrary time-varying accelerations occupy
the two-step nilpotent translation/time ideal. -/
theorem zero_rotation_triple (a b c : Vec3) :
    input a 0*(input b 0*input c 0-input c 0*input b 0)-
      (input b 0*input c 0-input c 0*input b 0)*input a 0 = 0 :=
  Magnus.ideal_triple_commutator 0 a 0 b 0 c 1 1 1

/-- Angular speed and thrust magnitude may both vary arbitrarily along a
single fixed axis. The only second bracket is a position translation. -/
theorem coaxial_commutator (k : Vec3) (a w b z : ℝ) :
    input (a • k) (w • k)*input (b • k) (z • k)-
      input (b • k) (z • k)*input (a • k) (w • k) =
      Magnus.ideal ((a-b) • k) 0 0 := by
  rw [input_commutator]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairCoordinates, crossProduct] <;> ring_nf <;> simp

theorem coaxial_triple (k : Vec3) (a w b z c y : ℝ) :
    input (a • k) (w • k)*
        (input (b • k) (z • k)*input (c • k) (y • k)-
          input (c • k) (y • k)*input (b • k) (z • k))-
      (input (b • k) (z • k)*input (c • k) (y • k)-
        input (c • k) (y • k)*input (b • k) (z • k))*input (a • k) (w • k) = 0 := by
  rw [coaxial_commutator]
  change _*Magnus.extended _ 0-Magnus.extended _ 0*_ = _
  rw [bracket_with_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Magnus.extended, hat, kinematicC, crossProduct] <;> ring_nf <;> simp

/-- Constant axial acceleration even permits arbitrary changing axial
angular speed with pairwise commuting input generators. -/
theorem coaxial_constant_acceleration_commutes (k : Vec3) (a w z : ℝ) :
    Commute (input (a • k) (w • k)) (input (a • k) (z • k)) := by
  show _*_ = _*_
  apply sub_eq_zero.mp
  rw [coaxial_commutator, sub_self, zero_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Magnus.ideal, Magnus.extended, hat, kinematicC]

end GNC.InputMagnus
