import GNC.Applications.ApproachGate.Invariant
import GNC.Analysis.ForcedParametricBox

/-! Force-commanded spatial burn/coast model with reciprocal mass.

The first eleven coordinates reuse the rotating-frame inverse-square model.
Coordinate 11 is m_initial/m - 1; coordinate 12 is a constant normalized
mass-flow coefficient beta. The commanded vector u is force divided by the
initial mass and reference acceleration scale. Therefore the delivered
acceleration multiplies u by 1+z[11]. The scalar on selects mass depletion
(one during the burn, zero in coast); the coast force command must also be
zero. An arbitrary three-dimensional additive acceleration history enters
only the velocity equations. It does not alter the phase or mass constraints.

This is a model and certificate interface, not a claim that any numerical
mission or particular motor/controller has already satisfied the interface.
-/
namespace GNC.MotorBurn
open PolynomialODE Matrix
abbrev Law := ApproachGate.Law

def firstIndex (i : Fin 11) : Fin 13 := ⟨i.val, by omega⟩

def embed : Expr 11 → Expr 13
  | .constant c => .constant c
  | .var i => .var (firstIndex i)
  | .add a b => .add (embed a) (embed b)
  | .multiply a b => .multiply (embed a) (embed b)
  | .negate a => .negate (embed a)

noncomputable section

def first (z : Fin 13 → ℝ) : Fin 11 → ℝ := fun i => z (firstIndex i)
def project (z : Fin 13 → ℝ) : Fin 6 → ℝ := ApproachGate.project (first z)
def inverseDefect (z : Fin 13 → ℝ) : ℝ := ApproachGate.inverseDefect (first z)
def phaseDefect (phase : ℝ) (z : Fin 13 → ℝ) : ℝ := ApproachGate.phaseDefect phase (first z)

def rate (mode : Law) (u : Fin 2 → ℝ) (on : ℝ) (z : Fin 13 → ℝ) (w : Vec3) : Fin 13 → ℝ :=
  let base := ApproachGate.rate mode u (first z)
  let force := ApproachGate.forceComponents mode u (z 7) (z 8) (z 9) (z 10)
  ![base 0,base 1,base 2,
    base 3+z 11*force 0+w 0,base 4+z 11*force 1+w 1,base 5+z 11*force 2+w 2,
    base 6,base 7,base 8,base 9,base 10,on*z 12*(1+z 11)^2,0]

def inputLift (w : Vec3) : Fin 13 → ℝ := ![0,0,0,w 0,w 1,w 2,0,0,0,0,0,0,0]
def mass (initialMass : ℝ) (z : Fin 13 → ℝ) : ℝ := initialMass/(1+z 11)

theorem embed_value (e : Expr 11) (z : Fin 13 → ℝ) :
    (embed e).value z = e.value (first z) := by
  induction e with
  | constant c => rfl
  | var i => rfl
  | add a b ha hb => simp only [embed, Expr.value, ha, hb]
  | multiply a b ha hb => simp only [embed, Expr.value, ha, hb]
  | negate a ha => simp only [embed, Expr.value, ha]

theorem rate_input (mode : Law) (u : Fin 2 → ℝ) (on : ℝ) (z : Fin 13 → ℝ) (w : Vec3) :
    rate mode u on z w = rate mode u on z 0+inputLift w := by
  ext i
  fin_cases i <;> simp [rate, inputLift]

end

def field (mode : Law) (u : Fin 2 → ℚ) (on : ℚ) : Fin 13 → Expr 13 :=
  let base := fun i => embed (ApproachGate.field mode u i)
  let force := fun i => embed (ApproachGate.forceExpressions mode u i)
  let correction := fun i => (Expr.var 11).multiply (force i)
  let ratio := (Expr.constant 1).add (Expr.var 11)
  ![base 0,base 1,base 2,(base 3).add (correction 0),(base 4).add (correction 1),
    (base 5).add (correction 2),base 6,base 7,base 8,base 9,base 10,
    ((Expr.constant on).multiply (Expr.var 12)).multiply (ratio.multiply ratio),.constant 0]

noncomputable section
open Set

theorem field_value (mode : Law) (u : Fin 2 → ℚ) (on : ℚ) (z : Fin 13 → ℝ) (i : Fin 13) :
    (field mode u on i).value z = rate mode (fun j => (u j : ℝ)) on z 0 i := by
  fin_cases i <;> simp [field, rate, Expr.value, embed_value,
    ApproachGate.field_value, ApproachGate.forceExpressions_value, first, firstIndex, pow_two]

/-- The inverse-radius constraint derivative is unchanged by variable mass
and arbitrary acceleration input; the proof retains the full gravity field. -/
theorem inverse_defect_derivative {z : ℝ → Fin 13 → ℝ} {t on : ℝ}
    {mode : Law} {u : Fin 2 → ℝ} {w : Vec3}
    (hz : HasDerivAt z (rate mode u on (z t) w) t) (hU : z t 6+1 ≠ 0) :
    HasDerivAt (fun s => inverseDefect (z s)) 0 t := by
  have h0 := hasDerivAt_pi.mp hz 0
  have h1 := hasDerivAt_pi.mp hz 1
  have h2 := hasDerivAt_pi.mp hz 2
  have h6 := hasDerivAt_pi.mp hz 6
  convert (((h6.add_const 1).inv hU).pow 2).sub
    ((((h0.const_add 1).pow 2).add (h1.pow 2)).add (h2.pow 2)) using 1
  simp [rate, ApproachGate.rate, first, firstIndex]
  field_simp
  <;> ring

theorem phase_defect_derivative {z : ℝ → Fin 13 → ℝ} {t start on : ℝ}
    {mode : Law} {u : Fin 2 → ℝ} {w : Vec3}
    (hz : HasDerivAt z (rate mode u on (z t) w) t) :
    HasDerivAt (fun s => phaseDefect (start+s) (z s)) 0 t := by
  have hc := ((hasDerivAt_pi.mp hz 9).sub ((hasDerivAt_id t).const_add start).cos).pow 2
  have hs := ((hasDerivAt_pi.mp hz 10).sub ((hasDerivAt_id t).const_add start).sin).pow 2
  convert hc.add hs using 1
  simp [rate, ApproachGate.rate, first, firstIndex]
  ring

theorem constant_parameters {z : ℝ → Fin 13 → ℝ} {T on : ℝ}
    {mode : Law} {u : Fin 2 → ℝ} {w : ℝ → Vec3}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt z (rate mode u on (z t) (w t)) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    z t 7 = z 0 7 ∧ z t 8 = z 0 8 ∧ z t 12 = z 0 12 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals apply ApproachGate.constant_on_interval (t := t) _ ht
  · intro s hs
    simpa [rate, ApproachGate.rate] using hasDerivAt_pi.mp (hz s hs) 7
  · intro s hs
    simpa [rate, ApproachGate.rate] using hasDerivAt_pi.mp (hz s hs) 8
  · intro s hs
    simpa [rate] using hasDerivAt_pi.mp (hz s hs) 12

/-- Reconstruct actual mass, with the same coefficient beta that appears in
the polynomial lift. Positivity follows from the certified reciprocal branch. -/
theorem mass_derivative {z : ℝ → Fin 13 → ℝ} {t on initialMass : ℝ}
    {mode : Law} {u : Fin 2 → ℝ} {w : Vec3}
    (hz : HasDerivAt z (rate mode u on (z t) w) t) (hm : 1+z t 11 ≠ 0) :
    HasDerivAt (fun s => mass initialMass (z s)) (-initialMass*on*z t 12) t := by
  have h := (hasDerivAt_pi.mp hz 11).const_add 1
  convert (hasDerivAt_const t initialMass).div h hm using 1
  simp [rate]
  field_simp
  <;> ring

theorem mass_positive {initialMass : ℝ} (hm : 0 < initialMass) (z : Fin 13 → ℝ)
    (hz : 0 < 1+z 11) : 0 < mass initialMass z := div_pos hm hz

/-- The force multiplier is exactly initial mass divided by current mass. -/
theorem mass_ratio {initialMass : ℝ} (hm : initialMass ≠ 0) (z : Fin 13 → ℝ)
    (hz : 1+z 11 ≠ 0) : initialMass/mass initialMass z = 1+z 11 := by
  unfold mass
  field_simp

/-- Projection recovers the full three-dimensional inverse-square equations
with force/mass acceleration and the actual additive disturbance. -/
theorem project_derivative {z : ℝ → Fin 13 → ℝ} {t θ phase on : ℝ}
    {mode : Law} {u : Fin 2 → ℝ} {w : Vec3}
    (hz : HasDerivAt z (rate mode u on (z t) w) t)
    (hU : z t 6+1 = (CircularRendezvous3D.radius (project (z t)))⁻¹)
    (hs : z t 7 = Real.sin θ) (hc : z t 8 = 1-Real.cos θ)
    (hC : z t 9 = Real.cos phase) (hS : z t 10 = Real.sin phase) :
    HasDerivAt (fun s => project (z s))
      (CircularRendezvous3D.physicalRate
        ((1+z t 11) • ApproachGate.source mode θ phase u+w) (project (z t))) t := by
  have he : z t 6 = (CircularRendezvous3D.radius (project (z t)))⁻¹-1 := by linarith
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [project, ApproachGate.project, rate, ApproachGate.rate, first, firstIndex,
      CircularRendezvous3D.physicalRate] using hasDerivAt_pi.mp hz 0
  · simpa [project, ApproachGate.project, rate, ApproachGate.rate, first, firstIndex,
      CircularRendezvous3D.physicalRate] using hasDerivAt_pi.mp hz 1
  · simpa [project, ApproachGate.project, rate, ApproachGate.rate, first, firstIndex,
      CircularRendezvous3D.physicalRate] using hasDerivAt_pi.mp hz 2
  · convert hasDerivAt_pi.mp hz 3 using 1
    simp [project, ApproachGate.project, rate, ApproachGate.rate, first, firstIndex,
      CircularRendezvous3D.physicalRate, ApproachGate.source_components, hs, hc, hC, hS, he,
      div_eq_mul_inv]
    ring
  · convert hasDerivAt_pi.mp hz 4 using 1
    simp [project, ApproachGate.project, rate, ApproachGate.rate, first, firstIndex,
      CircularRendezvous3D.physicalRate, ApproachGate.source_components, hs, hc, hC, hS, he,
      div_eq_mul_inv]
    ring
  · convert hasDerivAt_pi.mp hz 5 using 1
    simp [project, ApproachGate.project, rate, ApproachGate.rate, first, firstIndex,
      CircularRendezvous3D.physicalRate, ApproachGate.source_components, hs, hc, hC, hS, he,
      div_eq_mul_inv]
    ring_nf

end
end GNC.MotorBurn
