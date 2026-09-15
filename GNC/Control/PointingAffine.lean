import GNC.Control.ThrustSupport

/-! Norm bounds for an affine response to one common pointing direction.
Accumulate the response columns before applying this bound. The first-order
term retains their pairing with the nominal response; only the quadratic
perturbation uses a norm bound. Rational squared budgets suffice throughout.
-/
noncomputable section
open Matrix
namespace GNC.ThrustSupport

def pointingAxis : Vec3 := ![0,0,1]

theorem pair_enorm_le (x y : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hs : x^2+y^2 ≤ r^2) : enorm ![x,y,0] ≤ r := by
  have hn := enorm_sq ![x,y,0]
  simp [lengthSq] at hn
  nlinarith [enorm_nonneg ![x,y,0]]

/-- A two-coordinate use of mathlib's Cauchy--Schwarz bound. -/
theorem pair_dot_le (x y u v : ℝ) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hx : x^2+y^2 ≤ r^2) (hu : u^2+v^2 ≤ s^2) :
    x*u+y*v ≤ r*s := by
  calc
    x*u+y*v = ![x,y,0] ⬝ᵥ ![u,v,0] := by simp [dotProduct, Fin.sum_univ_succ]
    _ ≤ enorm ![x,y,0]*enorm ![u,v,0] := dot_le_enorm _ _
    _ ≤ r*s := mul_le_mul (pair_enorm_le x y hr hx) (pair_enorm_le u v hs hu)
      (enorm_nonneg _) hr

/-- Separate the first-order transverse pointing disk from axial loss.
The radii may be rational outward bounds; no trigonometric oracle is used. -/
theorem cap_coordinates (q : Vec3) {κ ρ η : ℝ}
    (hq : q ∈ Cap pointingAxis κ) (hκ : 0 ≤ κ)
    (hρ : 1-κ^2 ≤ ρ^2) (hη : 1-κ ≤ η) :
    q 0^2+q 1^2 ≤ ρ^2 ∧ |q 2-1| ≤ η := by
  have hq2 : κ ≤ q 2 := by
    simpa [pointingAxis, dotProduct, Fin.sum_univ_succ] using hq.2
  have hsq : q 0^2+q 1^2+q 2^2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using hq.1
  have hupper : q 2 ≤ 1 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
  constructor
  · have hmul := mul_nonneg (sub_nonneg.mpr hq2) (show 0 ≤ q 2+κ by linarith)
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
    linarith

/-- Bound the response of two transverse columns using one Frobenius budget. -/
theorem transverse_response_le (a b : Vec3) (x y : ℝ) {ρ F : ℝ}
    (hρ : 0 ≤ ρ) (hF : 0 ≤ F) (hq : x^2+y^2 ≤ ρ^2)
    (hf : enorm a^2+enorm b^2 ≤ F^2) : enorm (x • a+y • b) ≤ ρ*F := by
  calc
    enorm (x • a+y • b) ≤ enorm (x • a)+enorm (y • b) := enorm_add_le _ _
    _ = |x| * enorm a+|y| * enorm b := by rw [enorm_smul, enorm_smul]
    _ ≤ ρ*F := pair_dot_le _ _ _ _ hρ hF (by simpa only [sq_abs] using hq) hf

/-- A common-bias affine norm certificate preserving the nominal cross term.
The hypotheses are scalar squared budgets, suitable for kernel-checked
rational polynomial enclosures. This does not sum independent burn errors. -/
theorem cap_affine_norm_le (p a b c q : Vec3) {κ ρ η N H C F G R : ℝ}
    (hq : q ∈ Cap pointingAxis κ) (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ)
    (hρsq : 1-κ^2 ≤ ρ^2) (hη : 1-κ ≤ η)
    (hp : enorm p^2 ≤ N) (hH : 0 ≤ H)
    (hcross : (p ⬝ᵥ a)^2+(p ⬝ᵥ b)^2 ≤ H^2) (hc : |p ⬝ᵥ c| ≤ C)
    (hF : 0 ≤ F) (hf : enorm a^2+enorm b^2 ≤ F^2) (hg : enorm c ≤ G)
    (hR : 0 ≤ R) (hbudget : N+2*(ρ*H+η*C)+(ρ*F+η*G)^2 ≤ R^2) :
    enorm (p+q 0 • a+q 1 • b+(q 2-1) • c) ≤ R := by
  obtain ⟨htrans,haxial⟩ := cap_coordinates q hq hκ hρsq hη
  have hη0 : 0 ≤ η := (abs_nonneg _).trans haxial
  have hG : 0 ≤ G := (enorm_nonneg c).trans hg
  let d := q 0 • a+q 1 • b+(q 2-1) • c
  have hd : enorm d ≤ ρ*F+η*G := by
    calc
      enorm d ≤ enorm (q 0 • a+q 1 • b)+enorm ((q 2-1) • c) := enorm_add_le _ _
      _ = enorm (q 0 • a+q 1 • b)+|q 2-1| * enorm c := by rw [enorm_smul]
      _ ≤ ρ*F+η*G := add_le_add (transverse_response_le a b _ _ hρ hF htrans hf)
        (mul_le_mul haxial hg (enorm_nonneg c) hη0)
  have hlinear : p ⬝ᵥ d ≤ ρ*H+η*C := by
    have ht := pair_dot_le (q 0) (q 1) (p ⬝ᵥ a) (p ⬝ᵥ b) hρ hH htrans hcross
    have ha : (q 2-1)*(p ⬝ᵥ c) ≤ η*C := by
      calc
        _ ≤ |(q 2-1)*(p ⬝ᵥ c)| := le_abs_self _
        _ = |q 2-1| * |p ⬝ᵥ c| := abs_mul _ _
        _ ≤ η*C := mul_le_mul haxial hc (abs_nonneg _) hη0
    dsimp only [d]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    nlinarith
  have he : enorm (p+d)^2 = enorm p^2+2*(p ⬝ᵥ d)+enorm d^2 := by
    simp only [enorm_sq, ← dot_self_lengthSq, add_dotProduct, dotProduct_add,
      dotProduct_comm d p]
    ring
  have hB : 0 ≤ ρ*F+η*G := add_nonneg (mul_nonneg hρ hF) (mul_nonneg hη0 hG)
  have hd2 := mul_nonneg (sub_nonneg.mpr hd) (add_nonneg hB (enorm_nonneg d))
  have hresult : enorm (p+d) ≤ R := by nlinarith [enorm_nonneg (p+d)]
  simpa only [d, add_assoc] using hresult

/-- Orthogonal accumulated transverse columns remove the first-order norm
cross term. The axial loss and the squared transverse radius remain. -/
theorem orthogonal_cap_affine_norm_le (p a b c q : Vec3) {κ ρ η N C F G R : ℝ}
    (hq : q ∈ Cap pointingAxis κ) (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ)
    (hρsq : 1-κ^2 ≤ ρ^2) (hη : 1-κ ≤ η)
    (hp : enorm p^2 ≤ N) (ha : p ⬝ᵥ a = 0) (hb : p ⬝ᵥ b = 0)
    (hc : |p ⬝ᵥ c| ≤ C) (hF : 0 ≤ F) (hf : enorm a^2+enorm b^2 ≤ F^2)
    (hg : enorm c ≤ G) (hR : 0 ≤ R)
    (hbudget : N+2*η*C+(ρ*F+η*G)^2 ≤ R^2) :
    enorm (p+q 0 • a+q 1 • b+(q 2-1) • c) ≤ R := by
  apply cap_affine_norm_le p a b c q hq hκ hρ hρsq hη hp (le_refl 0)
    (by simp [ha, hb]) hc hF hf hg hR
  nlinarith

end GNC.ThrustSupport
