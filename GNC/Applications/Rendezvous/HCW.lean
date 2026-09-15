import GNC.Lie.Vector3

noncomputable section
open Matrix
namespace GNC

/-- Equations (39) and (40), with Ω=(0,0,n), expanded in LVLH coordinates. -/
def CircularLogODE (n : ℝ) (q u : ℝ → Vec3) : Prop := ∀ t,
  HasDerivAt (fun s => q s 0) (u t 0 + n * q t 1) t ∧
  HasDerivAt (fun s => q s 1) (u t 1 - n * q t 0) t ∧
  HasDerivAt (fun s => q s 2) (u t 2) t ∧
  HasDerivAt (fun s => u s 0) (2 * n ^ 2 * q t 0 + n * u t 1) t ∧
  HasDerivAt (fun s => u s 1) (-n ^ 2 * q t 1 - n * u t 0) t ∧
  HasDerivAt (fun s => u s 2) (-n ^ 2 * q t 2) t

/-- Actual second derivative statements for all three HCW equations (36)–(38). -/
theorem hcw_recovery (n : ℝ) (q u : ℝ → Vec3) (h : CircularLogODE n q u) (t : ℝ) :
    HasDerivAt (fun s => deriv (fun τ => q τ 0) s)
      (3 * n ^ 2 * q t 0 + 2 * n * deriv (fun s => q s 1) t) t ∧
    HasDerivAt (fun s => deriv (fun τ => q τ 1) s)
      (-2 * n * deriv (fun s => q s 0) t) t ∧
    HasDerivAt (fun s => deriv (fun τ => q τ 2) s) (-n ^ 2 * q t 2) t := by
  have d0 : (fun s => deriv (fun τ => q τ 0) s) = fun s => u s 0 + n * q s 1 :=
    funext fun s => (h s).1.deriv
  have d1 : (fun s => deriv (fun τ => q τ 1) s) = fun s => u s 1 - n * q s 0 :=
    funext fun s => (h s).2.1.deriv
  have d2 : (fun s => deriv (fun τ => q τ 2) s) = fun s => u s 2 :=
    funext fun s => (h s).2.2.1.deriv
  obtain ⟨hp0, hp1, hp2, hv0, hv1, hv2⟩ := h t
  rw [d0, d1, d2, hp0.deriv, hp1.deriv]
  refine ⟨?_, ?_, hv2⟩
  · convert hv0.add (hp1.const_mul n) using 1; ring
  · convert hv1.sub (hp0.const_mul n) using 1; ring

/-- Evaluating the vector equations really gives the scalar ODE used above. -/
theorem circular_vector_field (n : ℝ) (q u : Vec3) :
    u - ![0, 0, n] ⨯₃ q = ![u 0 + n*q 1, u 1 - n*q 0, u 2] ∧
    ![2*n^2*q 0, -n^2*q 1, -n^2*q 2] - ![0, 0, n] ⨯₃ u =
      ![2*n^2*q 0 + n*u 1, -n^2*q 1 - n*u 0, -n^2*q 2] := by
  constructor <;> ext i <;> fin_cases i <;> simp [cross_apply]

end GNC
