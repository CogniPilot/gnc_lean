import GNC.Magnus.FohSharpResidual

/-! All nested rotational brackets of two generators close on three vectors.
This is a statement about the Lie algebra basis, not termination of Magnus. -/
noncomputable section
namespace GNC.Magnus
open Matrix
open scoped Matrix

def fohDot (x y : Vec3) : ℝ := x 0*y 0+x 1*y 1+x 2*y 2

def fohBasis (w s : Vec3) (a b c : ℝ) : Vec3 :=
  a • w+b • s+c • (w ⨯₃ s)

set_option maxHeartbeats 4000000 in
theorem fohBasis_cross (w s : Vec3) (a b c d e j : ℝ) :
    fohBasis w s a b c ⨯₃ fohBasis w s d e j =
    fohBasis w s
      (fohDot w s*(a*j-c*d)+fohDot s s*(b*j-c*e))
      (-fohDot w w*(a*j-c*d)-fohDot w s*(b*j-c*e))
      (a*e-b*d) := by
  ext i
  fin_cases i <;> simp [fohBasis, fohDot, cross_apply, Matrix.vecHead, Matrix.vecTail, smul_eq_mul] <;> ring

inductive FohRotationalExpression where
  | first
  | second
  | bracket (x y : FohRotationalExpression)
  | add (x y : FohRotationalExpression)
  | scale (r : ℝ) (x : FohRotationalExpression)

def FohRotationalExpression.eval (w s : Vec3) : FohRotationalExpression → Vec3
  | .first => w
  | .second => s
  | .bracket x y => x.eval w s ⨯₃ y.eval w s
  | .add x y => x.eval w s+y.eval w s
  | .scale r x => r • x.eval w s

/-- All-depth closure: no new vector directions appear at higher order. -/
theorem foh_rotational_expression_basis (w s : Vec3) (x : FohRotationalExpression) :
    ∃ a b c : ℝ, x.eval w s = fohBasis w s a b c := by
  induction x with
  | first => exact ⟨1,0,0,by simp [FohRotationalExpression.eval, fohBasis]⟩
  | second => exact ⟨0,1,0,by simp [FohRotationalExpression.eval, fohBasis]⟩
  | bracket x y hx hy =>
    obtain ⟨a,b,c,hx⟩ := hx
    obtain ⟨d,e,j,hy⟩ := hy
    simp only [FohRotationalExpression.eval, hx, hy, fohBasis_cross]
    exact ⟨_,_,_,rfl⟩
  | add x y hx hy =>
    obtain ⟨a,b,c,hx⟩ := hx
    obtain ⟨d,e,j,hy⟩ := hy
    refine ⟨a+d,b+e,c+j,?_⟩
    simp only [FohRotationalExpression.eval, hx, hy, fohBasis, add_smul]
    abel
  | scale r x hx =>
    obtain ⟨a,b,c,hx⟩ := hx
    refine ⟨r*a,r*b,r*c,?_⟩
    simp [FohRotationalExpression.eval, hx, fohBasis, smul_add, smul_smul]

end GNC.Magnus
