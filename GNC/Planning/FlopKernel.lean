import GNC.Planning.PolynomialKernel

/-! A scalar arithmetic-operation model for small optimized query kernels.
Inputs and loads cost zero; each add or multiply costs one (FMA costs two).
Counts describe these algebraic algorithms, not compiler instructions or an
optimality claim. Transcendental implementations and proof arithmetic are
separate; neither is assigned a fictitious unit FLOP cost.
-/
namespace GNC.Planning.FlopKernel
variable {K : Type*} [CommSemiring K]

structure Value (K : Type*) where
  value : K
  flops : ℕ

def input (x : K) : Value K := ⟨x,0⟩
def add (x y : Value K) : Value K := ⟨x.value+y.value,x.flops+y.flops+1⟩
def mul (x y : Value K) : Value K := ⟨x.value*y.value,x.flops+y.flops+1⟩

def horner : List K → K → Value K
  | [], _ => input 0
  | [a], _ => input a
  | a :: b :: rest, x => add (input a) (mul (input x) (horner (b :: rest) x))

theorem horner_value (cs : List K) (x : K) :
    (horner cs x).value = PolynomialKernel.evaluate cs x := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    cases cs with
    | nil => simp [horner,input,PolynomialKernel.evaluate]
    | cons b rest => simp [horner,add,mul,input,PolynomialKernel.evaluate,ih]

theorem horner_flops (cs : List K) (x : K) :
    (horner cs x).flops = 2*(cs.length-1) := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    cases cs with
    | nil => rfl
    | cons b rest => simp [horner,add,mul,input,ih]; omega

/-- A state-transition polynomial has zero constant error at the nominal
command. Factoring out x avoids a redundant final addition to zero. -/
def zeroConstant (cs : List K) (x : K) : Value K :=
  match cs with
  | [] => input 0
  | _ :: _ => mul (input x) (horner cs x)

theorem zeroConstant_value (cs : List K) (x : K) :
    (zeroConstant cs x).value = PolynomialKernel.evaluate (0::cs) x := by
  cases cs with
  | nil => simp [zeroConstant,input,PolynomialKernel.evaluate]
  | cons a cs => simp [zeroConstant,mul,input,horner_value,PolynomialKernel.evaluate]

theorem zeroConstant_flops (cs : List K) (x : K) (h : cs ≠ []) :
    (zeroConstant cs x).flops = 2*cs.length-1 := by
  cases cs with
  | nil => contradiction
  | cons a cs => simp [zeroConstant,mul,input,horner_flops]; omega

def linearAngle (s c S C : K) : Value K :=
  add (mul (input s) (input S)) (mul (input c) (input C))

theorem linearAngle_value (s c S C : K) : (linearAngle s c S C).value = s*S+c*C := rfl
theorem linearAngle_flops (s c S C : K) : (linearAngle s c S C).flops = 3 := rfl

/-- One component of the reduced four-column quadratic gravity response.
Phase values s and c are shared inputs, computed once for all components. -/
def quadraticAngle (s c S C U V : K) : Value K :=
  add (mul (input s) (add (input S) (mul (input c) (input U))))
    (mul (input c) (add (input C) (mul (input c) (input V))))

theorem quadraticAngle_value (s c S C U V : K) :
    (quadraticAngle s c S C U V).value = s*(S+c*U)+c*(C+c*V) := rfl

theorem quadraticAngle_flops (s c S C U V : K) :
    (quadraticAngle s c S C U V).flops = 7 := rfl

end GNC.Planning.FlopKernel
