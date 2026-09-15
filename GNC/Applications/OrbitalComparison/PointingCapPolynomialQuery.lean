import GNC.Analysis.PolynomialBallMap
import GNC.Analysis.BernsteinRectangleTree
import GNC.Applications.OrbitalComparison.PointingCapClearance
import GNC.Applications.OrbitalComparison.PointingCapChart

/-! A polynomial-zonotope support query on the exact transverse disk.
The cubic cube-to-disk map adds no domain approximation. A reconstructed
Bernstein rectangle tree supplies the upper bound, and a feasible cube
witness supplies the lower bound. Both include the physical flow error.
-/
namespace GNC.OrbitalComparison.PointingCapPolynomialQuery
open BivariatePolynomial BivariateBernstein PointingCapCertificate
open PointingCapBurn PointingCapClearance PolynomialBallMap Set

def cubicU (σ : ℚ) : Coefficients := [[0],[3*σ/2,0,-σ/2],[],[-σ/2]]
def cubicV (σ : ℚ) : Coefficients := [[0,3*σ/2,0,-σ/2],[],[0,-σ/2]]

theorem value_cubicU (σ : ℚ) (a b : ℝ) :
    value (cubicU σ) a b = (σ:ℝ)*diskX a b := by
  simp [cubicU, value, slice, row, Planning.PolynomialKernel.evaluate, diskX]
  ring

theorem value_cubicV (σ : ℚ) (a b : ℝ) :
    value (cubicV σ) a b = (σ:ℝ)*diskX b a := by
  simp [cubicV, value, slice, row, Planning.PolynomialKernel.evaluate, diskX]
  ring

def lifted (p : Coefficients) (σ : ℚ) : Coefficients :=
  compose p (cubicU σ) (cubicV σ)

theorem value_lifted (p : Coefficients) (σ : ℚ) (a b : ℝ) :
    value (lifted p σ) a b = value p ((σ:ℝ)*diskX a b) ((σ:ℝ)*diskX b a) := by
  rw [lifted, value_compose, value_cubicU, value_cubicV]

theorem disk_upper (p : Coefficients) {σ : ℚ} (hs : 0 < σ)
    {n m : ℕ} (tree : BernsteinRectangleTree.Tree n m) (upper : ℚ)
    (hc : BernsteinRectangleTree.check (lifted p σ) upper tree (-1) 1 (-1) 1 = true)
    {u v : ℝ} (huv : u^2+v^2 ≤ (σ:ℝ)^2) : value p u v ≤ (upper:ℝ) := by
  obtain ⟨a,b,ha,hb,hu,hv⟩ := scaled_disk_surjective
    (show (0:ℝ)<σ by exact_mod_cast hs) huv
  have h := BernsteinRectangleTree.check_sound (lifted p σ) upper tree
    (by norm_num) (by norm_num) hc (by simpa using abs_le.mp ha) (by simpa using abs_le.mp hb)
  rw [value_lifted,hu,hv] at h
  exact h

noncomputable section

theorem support_upper (D : Data) (h : D.Valid) (ha : D.alpha=2)
    (upper : ℝ) (hb : ∀ x, Admissible (D.sigma:ℝ) x →
      ParameterPolynomial.value (projection D) x 1 ≤ upper) :
    support D ≤ upper+(D.positionError:ℝ) := by
  have hz : Admissible (D.sigma:ℝ) (fun _ => 0) := by
    simp [Admissible, sq_nonneg]
  let X := D.trajectory h (fun _ => 0) hz
  apply csSup_le
  · exact ⟨_, ⟨X.p 1, ⟨fun _ => 0,hz,X,rfl⟩,rfl⟩⟩
  · rintro y ⟨z,⟨x,hx,Y,rfl⟩,rfl⟩
    have he := (abs_le.mp (physical_error D h ha hx Y)).2
    linarith [hb x hx]

theorem polynomial_support_upper (D : Data) (h : D.Valid) (ha : D.alpha=2)
    (p : Coefficients) (hp : ∀ x, ParameterPolynomial.value (projection D) x 1 =
      value p (x 0) (x 1)) (hs : 0 < D.sigma)
    {n m : ℕ} (tree : BernsteinRectangleTree.Tree n m) (upper : ℚ)
    (hc : BernsteinRectangleTree.check (lifted p D.sigma) upper tree (-1) 1 (-1) 1 = true) :
    support D ≤ (upper:ℝ)+(D.positionError:ℝ) := by
  apply support_upper D h ha
  intro x hx
  rw [hp]
  exact disk_upper p hs tree upper hc hx.2.2.2

theorem polynomial_support_lower (D : Data) (h : D.Valid) (ha : D.alpha=2)
    (p : Coefficients) (hp : ∀ x, ParameterPolynomial.value (projection D) x 1 =
      value p (x 0) (x 1)) (hs : (D.sigma:ℝ)^2 ≤ 1)
    (upper : ℝ) (hub : ∀ x, Admissible (D.sigma:ℝ) x →
      ParameterPolynomial.value (projection D) x 1 ≤ upper)
    (a b : ℚ) (ha' : |a| ≤ 1) (hb' : |b| ≤ 1) :
    (rationalValue (lifted p D.sigma) a b:ℝ)-(D.positionError:ℝ) ≤ support D := by
  let u : ℝ := (D.sigma:ℝ)*diskX (a:ℝ) (b:ℝ)
  let v : ℝ := (D.sigma:ℝ)*diskX (b:ℝ) (a:ℝ)
  let x := PointingCapChart.input u v
  have hx : Admissible (D.sigma:ℝ) x := PointingCapChart.admissible hs
    (scaled_disk_inside _ (by exact_mod_cast ha') (by exact_mod_cast hb'))
  let X := D.trajectory h x hx
  have he := (abs_le.mp (physical_error D h ha hx X)).1
  have hp' : ParameterPolynomial.value (projection D) x 1 =
      (rationalValue (lifted p D.sigma) a b:ℝ) := by
    rw [hp, rationalValue_cast, value_lifted]
    rfl
  rw [hp'] at he
  have hbounded : BddAbove ((fun z => observable (PointingCapObstruction.framed z)) ''
      D.reachablePositions 1) := by
    refine ⟨upper+(D.positionError:ℝ), ?_⟩
    rintro y ⟨z,⟨x,hx,Y,rfl⟩,rfl⟩
    have hh := (abs_le.mp (physical_error D h ha hx Y)).2
    linarith [hub x hx]
  have hw := le_csSup hbounded (show observable (PointingCapObstruction.framed (X.p 1)) ∈
      ((fun z => observable (PointingCapObstruction.framed z)) '' D.reachablePositions 1) from
      ⟨X.p 1,⟨x,hx,X,rfl⟩,rfl⟩)
  change _ ≤ sSup _
  linarith

end
end GNC.OrbitalComparison.PointingCapPolynomialQuery
