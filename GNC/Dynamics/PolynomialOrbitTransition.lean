import GNC.Analysis.PolynomialBox
import GNC.Dynamics.PolynomialOrbit

/-! Joint polynomial propagation of a planar inverse-radius reference and
the two blocks of its central-gravity variational equation. Reference thrust
is prescribed in the error equation, so its state derivative is not included.
-/
namespace GNC.PolynomialODE.Expr
variable {n m : ℕ}

def rename (e : Expr n) (indices : Fin n → Fin m) : Expr m :=
  match e with
  | constant c => constant c
  | var i => var (indices i)
  | add a b => add (a.rename indices) (b.rename indices)
  | multiply a b => multiply (a.rename indices) (b.rename indices)
  | negate a => negate (a.rename indices)

theorem value_rename (e : Expr n) (indices : Fin n → Fin m) (x : Fin m → ℝ) :
    (e.rename indices).value x = e.value (fun i => x (indices i)) := by
  induction e <;> simp_all [rename, value]

end GNC.PolynomialODE.Expr

namespace GNC.PolynomialOrbitTransition
open PolynomialODE

def referenceIndex (i : Fin 5) : Fin 25 := ⟨i, by omega⟩
def planeIndex (i j : Fin 4) : Fin 25 := ⟨5+4*i.val+j.val, by omega⟩
def normalIndex (i j : Fin 2) : Fin 25 := ⟨21+2*i.val+j.val, by omega⟩

def planeField (i j : Fin 4) : Expr 25 :=
  let x := Expr.var 0
  let y := Expr.var 1
  let u := Expr.var 4
  let u3 := u.multiply (u.multiply u)
  let u5 := u3.multiply (u.multiply u)
  let dxx := ((Expr.constant 3).multiply (u5.multiply (x.multiply x))).add u3.negate
  let dxy := (Expr.constant 3).multiply (u5.multiply (x.multiply y))
  let dyy := ((Expr.constant 3).multiply (u5.multiply (y.multiply y))).add u3.negate
  ![Expr.var (planeIndex 2 j), Expr.var (planeIndex 3 j),
    (dxx.multiply (.var (planeIndex 0 j))).add (dxy.multiply (.var (planeIndex 1 j))),
    (dxy.multiply (.var (planeIndex 0 j))).add (dyy.multiply (.var (planeIndex 1 j)))] i

def normalField (i j : Fin 2) : Expr 25 :=
  let u := Expr.var 4
  let u3 := u.multiply (u.multiply u)
  ![Expr.var (normalIndex 1 j), (u3.multiply (.var (normalIndex 0 j))).negate] i

def field (a : ℚ) (k : Fin 25) : Expr 25 :=
  if hk : k.val < 5 then
    (PolynomialOrbit.field a ⟨k.val,hk⟩).rename referenceIndex
  else if hk' : k.val < 21 then
    planeField ⟨(k.val-5)/4, by omega⟩ ⟨(k.val-5)%4, by omega⟩
  else
    normalField ⟨(k.val-21)/2, by omega⟩ ⟨(k.val-21)%2, by omega⟩

def pack {K : Type*} (z : Fin 5 → K) (F : Matrix (Fin 4) (Fin 4) K)
    (H : Matrix (Fin 2) (Fin 2) K) (k : Fin 25) : K :=
  if hk : k.val < 5 then z ⟨k.val,hk⟩
  else if hk' : k.val < 21 then
    F ⟨(k.val-5)/4, by omega⟩ ⟨(k.val-5)%4, by omega⟩
  else H ⟨(k.val-21)/2, by omega⟩ ⟨(k.val-21)%2, by omega⟩

theorem pack_reference {K : Type*} (z : Fin 5 → K) (F H) (i : Fin 5) :
    pack z F H (referenceIndex i) = z i := by
  fin_cases i <;> rfl

theorem pack_plane {K : Type*} (z : Fin 5 → K) (F H) (i j : Fin 4) :
    pack z F H (planeIndex i j) = F i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem pack_normal {K : Type*} (z : Fin 5 → K) (F H) (i j : Fin 2) :
    pack z F H (normalIndex i j) = H i j := by
  fin_cases i <;> fin_cases j <;> rfl

def planeGenerator {K : Type*} [CommRing K] (z : Fin 5 → K) : Matrix (Fin 4) (Fin 4) K :=
  !![0,0,1,0; 0,0,0,1;
    3*z 4^5*z 0^2-z 4^3, 3*z 4^5*z 0*z 1, 0,0;
    3*z 4^5*z 0*z 1, 3*z 4^5*z 1^2-z 4^3, 0,0]

def normalGenerator {K : Type*} [CommRing K] (z : Fin 5 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![0,1; -z 4^3,0]

set_option maxHeartbeats 2000000 in
/-- The executable expression system is precisely the lifted reference and
the two central-gravity transition matrix equations. -/
theorem field_pack (a : ℚ) (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 25) :
    (field a k).value (pack z F H) =
      pack (PolynomialOrbit.rate a z) (planeGenerator z * F) (normalGenerator z * H) k := by
  fin_cases k <;>
    norm_num [field, planeField, normalField, Expr.rename, Expr.value, pack,
      referenceIndex, planeIndex, normalIndex, PolynomialOrbit.field, PolynomialOrbit.rate,
      planeGenerator, normalGenerator, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> ring_nf <;> simp <;> ring

theorem pack_derivative {z dz : ℝ → Fin 5 → ℝ}
    {F dF : ℝ → Matrix (Fin 4) (Fin 4) ℝ}
    {H dH : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {t : ℝ}
    (hz : HasDerivAt z (dz t) t) (hF : HasDerivAt F (dF t) t)
    (hH : HasDerivAt H (dH t) t) :
    HasDerivAt (fun s => pack (z s) (F s) (H s)) (pack (dz t) (dF t) (dH t)) t := by
  apply hasDerivAt_pi.mpr
  intro k
  by_cases hk : k.val < 5
  · simpa only [pack, dif_pos hk] using hasDerivAt_pi.mp hz ⟨k.val,hk⟩
  · by_cases hk' : k.val < 21
    · simpa only [pack, dif_neg hk, dif_pos hk'] using
        hasDerivAt_pi.mp (hasDerivAt_pi.mp hF ⟨(k.val-5)/4,by omega⟩) ⟨(k.val-5)%4,by omega⟩
    · simpa only [pack, dif_neg hk, dif_neg hk'] using
        hasDerivAt_pi.mp (hasDerivAt_pi.mp hH ⟨(k.val-21)/2,by omega⟩) ⟨(k.val-21)%2,by omega⟩

theorem joint_derivative (a : ℚ) {z : ℝ → Fin 5 → ℝ}
    {F : ℝ → Matrix (Fin 4) (Fin 4) ℝ} {H : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {t : ℝ}
    (hz : HasDerivAt z (PolynomialOrbit.rate a (z t)) t)
    (hF : HasDerivAt F (planeGenerator (z t) * F t) t)
    (hH : HasDerivAt H (normalGenerator (z t) * H t) t) :
    HasDerivAt (fun s => pack (z s) (F s) (H s))
      (fun k => (field a k).value (pack (z t) (F t) (H t))) t := by
  simp_rw [field_pack]
  exact pack_derivative (dz := fun s => PolynomialOrbit.rate a (z s))
    (dF := fun s => planeGenerator (z s) * F s)
    (dH := fun s => normalGenerator (z s) * H s) hz hF hH

theorem pack_continuous {z : ℝ → Fin 5 → ℝ}
    {F : ℝ → Matrix (Fin 4) (Fin 4) ℝ} {H : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H) :
    Continuous (fun s => pack (z s) (F s) (H s)) := by
  apply continuous_pi
  intro k
  by_cases hk : k.val < 5
  · simpa only [pack, dif_pos hk] using (continuous_apply ⟨k.val,hk⟩).comp hz
  · by_cases hk' : k.val < 21
    · simpa only [pack, dif_neg hk, dif_pos hk'] using
        (continuous_apply ⟨(k.val-5)%4,by omega⟩).comp
          ((continuous_apply ⟨(k.val-5)/4,by omega⟩).comp hF)
    · simpa only [pack, dif_neg hk, dif_neg hk'] using
        (continuous_apply ⟨(k.val-21)%2,by omega⟩).comp
          ((continuous_apply ⟨(k.val-21)/2,by omega⟩).comp hH)

end GNC.PolynomialOrbitTransition
