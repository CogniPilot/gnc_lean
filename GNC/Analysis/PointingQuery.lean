import GNC.Planning.FlopKernel

/-! Factored arithmetic for a transverse quartic. The squared radius is
computed once and reused; preparation of time coefficients is separate.
These are counts for explicit algorithms, not optimality lower bounds. -/
namespace GNC.PointingQuery
open Planning.FlopKernel
variable {K : Type*} [CommSemiring K]

def radiusSquared (u v : K) : Value K :=
  add (mul (input u) (input u)) (mul (input v) (input v))

def planar (u h L Q B A G : K) : Value K :=
  add (mul (input u)
    (add (add (input L) (mul (input G) (input h))) (mul (input Q) (input u))))
    (mul (input h) (add (input B) (mul (input A) (input h))))

def normal (u v h L B G : K) : Value K :=
  mul (input v) (add (add (input L) (mul (input B) (input u)))
    (mul (input G) (input h)))

theorem radiusSquared_value (u v : K) : (radiusSquared u v).value=u^2+v^2 := by
  simp [radiusSquared,Planning.FlopKernel.add,Planning.FlopKernel.mul,input,pow_two]

theorem planar_value (u h L Q B A G : K) :
    (planar u h L Q B A G).value=L*u+Q*u^2+B*h+G*u*h+A*h^2 := by
  simp only [planar,Planning.FlopKernel.add,Planning.FlopKernel.mul,input]
  ring

theorem normal_value (u v h L B G : K) :
    (normal u v h L B G).value=L*v+B*u*v+G*v*h := by
  simp only [normal,Planning.FlopKernel.add,Planning.FlopKernel.mul,input]
  ring

theorem radiusSquared_flops (u v : K) : (radiusSquared u v).flops=3 := rfl
theorem planar_flops (u h L Q B A G : K) : (planar u h L Q B A G).flops=9 := rfl
theorem normal_flops (u v h L B G : K) : (normal u v h L B G).flops=5 := rfl

/-- Count radius formation once, then use its value in the three outputs.
Fused multiply-add counts as two scalar operations. -/
theorem spatial_flops (u v L0 Q0 B0 A0 G0 L1 Q1 B1 A1 G1 L2 B2 G2 : K) :
    let h := radiusSquared u v
    h.flops+(planar u h.value L0 Q0 B0 A0 G0).flops+
      (planar u h.value L1 Q1 B1 A1 G1).flops+
      (normal u v h.value L2 B2 G2).flops=26 := rfl

/-- Subtraction has the same scalar cost as addition. -/
def subtract {F : Type*} [Sub F] (x y : Value F) : Value F :=
  ⟨x.value-y.value,x.flops+y.flops+1⟩

/-- If the physical radial deficit is already supplied, the sphere relation
computes the squared transverse radius with one subtraction and one multiply. -/
def radiusFromDepth {F : Type*} [CommRing F] (c : F) : Value F :=
  mul (input c) (subtract (input 2) (input c))

theorem radiusFromDepth_value {F : Type*} [CommRing F] (c : F) :
    (radiusFromDepth c).value=c*(2-c) := rfl

theorem radiusFromDepth_flops {F : Type*} [CommRing F] (c : F) :
    (radiusFromDepth c).flops=2 := rfl

end GNC.PointingQuery
