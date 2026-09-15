import GNC.Dynamics.CircularRendezvous3D
import GNC.Applications.OrbitalComparison.SpatialBurn
import GNC.Analysis.ParametricBox

/-! Physical lift for the specified spatial approach-gate study.

One pointing angle is shared by all burn and coast arcs. The force can be
fixed in target RTN or in inertial coordinates. Two phase states represent
the actual rotating frame. The inverse-radius state is centered at one to
avoid cancellation in the nominal gravity expression.
-/
namespace GNC.ApproachGate
open PolynomialODE Matrix

inductive Law where
  | rtn
  | inertial
  deriving DecidableEq

noncomputable section

def pointing (θ : ℝ) (u : Fin 2 → ℝ) : Vec3 :=
  rotate (OrbitalComparison.SpatialBurn.attitude θ) ![u 0,u 1,0]

def source (mode : Law) (θ phase : ℝ) (u : Fin 2 → ℝ) : Vec3 :=
  match mode with
  | .rtn => pointing θ u
  | .inertial => rotate (AxisRotation.zRotation (-phase)) (pointing θ u)

def forceComponents (mode : Law) (u : Fin 2 → ℝ) (s c C S : ℝ) : Vec3 :=
  let x := (1-c)*u 0-(4/5)*s*u 1
  let y := (4/5)*s*u 0+(1-(16/25)*c)*u 1
  let z := (3/5)*s*u 0-(12/25)*c*u 1
  match mode with
  | .rtn => ![x,y,z]
  | .inertial => ![C*x+S*y,-S*x+C*y,z]

theorem pointing_components (θ : ℝ) (u : Fin 2 → ℝ) :
    pointing θ u = forceComponents .rtn u (Real.sin θ) (1-Real.cos θ) 1 0 := by
  ext i
  fin_cases i <;>
    simp [pointing, forceComponents, rotate, OrbitalComparison.SpatialBurn.axisFrameMatrix,
      AxisRotation.zMatrix, mulVec, mul_apply, dotProduct, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail] <;> ring_nf <;> simp

theorem source_components (mode : Law) (θ phase : ℝ) (u : Fin 2 → ℝ) :
    source mode θ phase u =
      forceComponents mode u (Real.sin θ) (1-Real.cos θ) (Real.cos phase) (Real.sin phase) := by
  cases mode
  · exact pointing_components θ u
  · rw [source, pointing_components]
    ext i
    fin_cases i <;> simp [forceComponents, rotate, AxisRotation.zRotation,
      AxisRotation.zMatrix, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

def lift (θ phase : ℝ) (w : Fin 6 → ℝ) : Fin 11 → ℝ :=
  ![w 0,w 1,w 2,w 3,w 4,w 5,(CircularRendezvous3D.radius w)⁻¹-1,
    Real.sin θ,1-Real.cos θ,Real.cos phase,Real.sin phase]

def rate (mode : Law) (u : Fin 2 → ℝ) (z : Fin 11 → ℝ) : Fin 11 → ℝ :=
  let η := z 6
  let gm1 := 3*η+3*η^2+η^3
  let ir3 := 1+gm1
  let a := forceComponents mode u (z 7) (z 8) (z 9) (z 10)
  ![z 3,z 4,z 5,
    2*z 4-(1+z 0)*gm1+a 0,
    -2*z 3-z 1*gm1+a 1,
    -z 2*ir3+a 2,
    -ir3*((1+z 0)*z 3+z 1*z 4+z 2*z 5),
    0,0,-z 10,z 9]

theorem lift_continuous {w : ℝ → Fin 6 → ℝ} (hw : Continuous w)
    (hr : ∀ t, 0 < CircularRendezvous3D.radius (w t)) (θ start : ℝ) :
    Continuous (fun t => lift θ (start+t) (w t)) := by
  have hc := CircularRendezvous3D.lift_continuous hw hr
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t => w t 0)
    exact (continuous_apply 0).comp hw
  · change Continuous (fun t => w t 1)
    exact (continuous_apply 1).comp hw
  · change Continuous (fun t => w t 2)
    exact (continuous_apply 2).comp hw
  · change Continuous (fun t => w t 3)
    exact (continuous_apply 3).comp hw
  · change Continuous (fun t => w t 4)
    exact (continuous_apply 4).comp hw
  · change Continuous (fun t => w t 5)
    exact (continuous_apply 5).comp hw
  · change Continuous (fun t => (CircularRendezvous3D.radius (w t))⁻¹ - 1)
    exact ((continuous_apply 6).comp hc).sub continuous_const
  · change Continuous (fun _ : ℝ => Real.sin θ)
    exact continuous_const
  · change Continuous (fun _ : ℝ => 1-Real.cos θ)
    exact continuous_const
  · change Continuous (fun t : ℝ => Real.cos (start+t))
    fun_prop
  · change Continuous (fun t : ℝ => Real.sin (start+t))
    fun_prop

theorem lift_derivative {w : ℝ → Fin 6 → ℝ} {mode : Law} {u : Fin 2 → ℝ}
    {θ start t : ℝ}
    (hw : HasDerivAt w (CircularRendezvous3D.physicalRate
      (source mode θ (start+t) u) (w t)) t)
    (hr : 0 < CircularRendezvous3D.radius (w t)) :
    HasDerivAt (fun s => lift θ (start+s) (w s))
      (rate mode u (lift θ (start+t) (w t))) t := by
  have hbase := CircularRendezvous3D.lift_derivative hw hr
  have hphase := (hasDerivAt_id t).const_add start
  have hs := source_components mode θ (start+t) u
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [lift, rate, CircularRendezvous3D.lift, CircularRendezvous3D.rate] using
      (hasDerivAt_pi.mp hbase 0)
  · simpa [lift, rate, CircularRendezvous3D.lift, CircularRendezvous3D.rate] using
      (hasDerivAt_pi.mp hbase 1)
  · simpa [lift, rate, CircularRendezvous3D.lift, CircularRendezvous3D.rate] using
      (hasDerivAt_pi.mp hbase 2)
  · convert hasDerivAt_pi.mp hbase 3 using 1
    simp [lift, rate, CircularRendezvous3D.lift, CircularRendezvous3D.rate, hs]
    ring
  · convert hasDerivAt_pi.mp hbase 4 using 1
    simp [lift, rate, CircularRendezvous3D.lift, CircularRendezvous3D.rate, hs]
    ring
  · convert hasDerivAt_pi.mp hbase 5 using 1
    simp [lift, rate, CircularRendezvous3D.lift, CircularRendezvous3D.rate, hs]
    ring_nf
    simp
  · convert (hasDerivAt_pi.mp hbase 6).sub_const 1 using 1
    simp [lift, rate, CircularRendezvous3D.lift, CircularRendezvous3D.rate]
    ring
  · simpa [lift, rate] using hasDerivAt_const t (Real.sin θ)
  · simpa [lift, rate] using hasDerivAt_const t (1-Real.cos θ)
  · simpa [lift, rate] using hphase.cos
  · simpa [lift, rate] using hphase.sin

end

def forceExpressions (mode : Law) (u : Fin 2 → ℚ) : Fin 3 → Expr 11 :=
  let s := Expr.var 7
  let c := Expr.var 8
  let C := Expr.var 9
  let S := Expr.var 10
  let x := ((Expr.constant (u 0)).add ((Expr.constant (-u 0)).multiply c)).add
    ((Expr.constant (-(4/5)*u 1)).multiply s)
  let y := ((Expr.constant (u 1)).add ((Expr.constant (-(16/25)*u 1)).multiply c)).add
    ((Expr.constant ((4/5)*u 0)).multiply s)
  let z := ((Expr.constant ((3/5)*u 0)).multiply s).add
    ((Expr.constant (-(12/25)*u 1)).multiply c)
  match mode with
  | .rtn => ![x,y,z]
  | .inertial => ![(C.multiply x).add (S.multiply y),
      (S.multiply x).negate.add (C.multiply y),z]

def field (mode : Law) (u : Fin 2 → ℚ) : Fin 11 → Expr 11 :=
  let x := Expr.var 0
  let y := Expr.var 1
  let z := Expr.var 2
  let vx := Expr.var 3
  let vy := Expr.var 4
  let vz := Expr.var 5
  let η := Expr.var 6
  let gm1 := ((Expr.constant 3).multiply η).add
    (((Expr.constant 3).multiply (η.multiply η)).add (η.multiply (η.multiply η)))
  let ir3 := (Expr.constant 1).add gm1
  let r := (Expr.constant 1).add x
  let a := forceExpressions mode u
  ![vx,vy,vz,
    ((Expr.constant 2).multiply vy).add (r.multiply gm1).negate |>.add (a 0),
    ((Expr.constant (-2)).multiply vx).add (y.multiply gm1).negate |>.add (a 1),
    (z.multiply ir3).negate.add (a 2),
    (ir3.multiply (((r.multiply vx).add (y.multiply vy)).add (z.multiply vz))).negate,
    .constant 0,.constant 0,(Expr.var 10).negate,Expr.var 9]

noncomputable section

theorem forceExpressions_value (mode : Law) (u : Fin 2 → ℚ) (z : Fin 11 → ℝ) (i : Fin 3) :
    (forceExpressions mode u i).value z =
      forceComponents mode (fun j => (u j : ℝ)) (z 7) (z 8) (z 9) (z 10) i := by
  cases mode <;> fin_cases i <;> simp [forceExpressions, forceComponents, Expr.value] <;> ring

theorem field_value (mode : Law) (u : Fin 2 → ℚ) (z : Fin 11 → ℝ) (i : Fin 11) :
    (field mode u i).value z = rate mode (fun j => (u j : ℝ)) z i := by
  fin_cases i <;> simp [field, rate, Expr.value, forceExpressions_value] <;> ring_nf <;> simp

end
end GNC.ApproachGate
