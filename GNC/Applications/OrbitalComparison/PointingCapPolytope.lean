import GNC.Applications.OrbitalComparison.PointingCapClearance
import GNC.Applications.OrbitalComparison.PointingCapRefinement

/-! Physical terminal support in arbitrary rational unit directions.
Every finite collection of checked queries encloses the entire physical
reachable family in their halfspace intersection. The supplied prediction
error is charged to both ends of every support interval. -/
namespace GNC.OrbitalComparison.PointingCapPolytope
open ParameterPolynomial PointingCapSupport PointingCapCertificate
open PointingCapBurn PointingCapRefinement SpatialBurn Set

def projection (D : Data) (n : Fin 3 → ℚ) : Coefficients :=
  add (scale (n 0) (D.q 0)) (add (scale (n 1) (D.q 1)) (scale (n 2) (D.q 2)))

def Unit (n : Fin 3 → ℚ) : Prop := n 0^2+n 1^2+n 2^2=1
instance (n : Fin 3 → ℚ) : Decidable (Unit n) := by unfold Unit; infer_instance

def Feasible (σ : ℚ) (x : Fin 3 → ℚ) : Prop :=
  0≤x 2 ∧ x 2≤1 ∧ x 0^2+x 1^2=2*x 2-x 2^2 ∧ x 0^2+x 1^2≤σ^2
instance (σ : ℚ) (x : Fin 3 → ℚ) : Decidable (Feasible σ x) := by
  unfold Feasible; infer_instance

structure Entry where
  normal : Fin 3 → ℚ
  certificate : Certificate
  witness : Fin 3 → ℚ
  lower : ℚ
  upper : ℚ

def Entry.Valid (E : Entry) (D : Data) (ε width : ℚ) : Prop :=
  Unit E.normal ∧ E.certificate.Valid (projection D E.normal) D.sigma ∧
  E.certificate.time=1 ∧ Feasible D.sigma E.witness ∧
  E.lower≤rationalValue (projection D E.normal) E.witness 1-ε ∧
  E.certificate.upper+ε≤E.upper ∧ E.upper-E.lower≤width
instance (E : Entry) (D : Data) (ε width : ℚ) : Decidable (E.Valid D ε width) := by
  unfold Entry.Valid; infer_instance

noncomputable section

def observable (n : Fin 3 → ℚ) (z : E3) : ℝ :=
  (n 0:ℝ)*z 0+(n 1:ℝ)*z 1+(n 2:ℝ)*z 2

theorem observable_norm (n : Fin 3 → ℚ) (hn : Unit n) (z : E3) :
    |observable n z|≤‖z‖ := by
  have hh : (n 0:ℝ)^2+(n 1:ℝ)^2+(n 2:ℝ)^2=1 := by exact_mod_cast hn
  have hnorm : ‖pack (n 0) (n 1) (n 2)‖=1 := by
    have h := pack_norm_sq (n 0) (n 1) (n 2)
    nlinarith [norm_nonneg (pack (n 0) (n 1) (n 2))]
  have hi : inner ℝ (pack (n 0) (n 1) (n 2)) z=observable n z := by
    change dotProduct z.ofLp (star (pack (n 0) (n 1) (n 2)).ofLp)=observable n z
    simp [pack_eq,dotProduct,Fin.sum_univ_succ,observable]
    ring
  simpa only [hi,hnorm,one_mul] using abs_real_inner_le_norm (pack (n 0) (n 1) (n 2)) z

theorem observable_sub (n : Fin 3 → ℚ) (z w : E3) :
    observable n (z-w)=observable n z-observable n w := by
  simp only [observable,PiLp.sub_apply]
  ring

theorem projection_value (D : Data) (n : Fin 3 → ℚ) (x : Fin 3 → ℝ) (t : ℝ) :
    value (projection D n) x t=observable n (D.displacement x t) := by
  simp [projection,value_add,value_scale,observable,Data.displacement,
    PointingCapPolynomial.vectorValue,pack_eq]
  ring

theorem feasible_cast {σ : ℚ} {x : Fin 3 → ℚ} (hx : Feasible σ x) :
    Admissible (σ:ℝ) (fun i => (x i:ℝ)) := by
  obtain ⟨h0,h1,hs,hd⟩ := hx
  refine ⟨?_,?_,?_,?_⟩
  · change 0≤(x 2:ℝ)
    exact_mod_cast h0
  · change (x 2:ℝ)≤1
    exact_mod_cast h1
  · change (x 0:ℝ)^2+(x 1:ℝ)^2=2*(x 2:ℝ)-(x 2:ℝ)^2
    exact_mod_cast hs
  · change (x 0:ℝ)^2+(x 1:ℝ)^2≤(σ:ℝ)^2
    exact_mod_cast hd

/-- An error guarantee for every solution, rather than a sampled candidate. -/
def PhysicalError (D : Data) (ε : ℚ) : Prop :=
  ∀ x, Admissible (D.sigma:ℝ) x → ∀ X : Motion (D.alpha:ℝ) (direction x),
    ‖X.p 1-D.position x 1‖≤(ε:ℝ)

theorem refined_error (D : Data) (hD : D.Valid) (B : Bounds)
    (hB : B.Sound D) (hC : B.Checks D) {ε : ℚ} (he : B.positionError D≤ε) :
    PhysicalError D ε := by
  intro x hx X
  exact ((B.certifies D hD hB hC hx X 1 (by norm_num)).1).trans (by exact_mod_cast he)

theorem physical_projection_error (D : Data) (ha : D.alpha=2)
    (n : Fin 3 → ℚ) (hn : Unit n) {ε : ℚ} (he : PhysicalError D ε)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x)
    (X : Motion (D.alpha:ℝ) (direction x)) :
    |observable n (PointingCapObstruction.framed (X.p 1))-
      value (projection D n) x 1|≤(ε:ℝ) := by
  rw [projection_value,←PointingCapClearance.candidate_frame D ha,←observable_sub]
  apply (observable_norm n hn _).trans
  rw [PointingCapObstruction.frame_difference]
  exact he x hx X

def support (D : Data) (n : Fin 3 → ℚ) : ℝ :=
  sSup ((fun z => observable n (PointingCapObstruction.framed z)) '' D.reachablePositions 1)

theorem support_eq {D₁ D₂ : Data} (ha : D₁.alpha=D₂.alpha) (hs : D₁.sigma=D₂.sigma)
    (n : Fin 3 → ℚ) : support D₁ n=support D₂ n := by
  unfold support
  rw [Data.reachablePositions_eq ha hs]

theorem Entry.physical_upper (E : Entry) (D : Data) (ha : D.alpha=2)
    {ε width : ℚ} (hE : E.Valid D ε width) (he : PhysicalError D ε)
    {x : Fin 3 → ℝ} (hx : Admissible (D.sigma:ℝ) x)
    (X : Motion (D.alpha:ℝ) (direction x)) :
    observable E.normal (PointingCapObstruction.framed (X.p 1))≤(E.upper:ℝ) := by
  obtain ⟨hn,hc,ht,_,_,hu,_⟩ := hE
  have hb := E.certificate.bounds (projection D E.normal) D.sigma hc hx
  rw [ht,Rat.cast_one] at hb
  have herr := (abs_le.mp (physical_projection_error D ha E.normal hn he hx X)).2
  have hu' : (E.certificate.upper:ℝ)+(ε:ℝ)≤(E.upper:ℝ) := by exact_mod_cast hu
  linarith

theorem Entry.support_interval (E : Entry) (D : Data) (hD : D.Valid) (ha : D.alpha=2)
    {ε width : ℚ} (hE : E.Valid D ε width) (he : PhysicalError D ε) :
    (E.lower:ℝ)≤support D E.normal ∧ support D E.normal≤(E.upper:ℝ) := by
  have hx := feasible_cast hE.2.2.2.1
  let X := D.trajectory hD (fun i => (E.witness i:ℝ)) hx
  let S := (fun z => observable E.normal (PointingCapObstruction.framed z)) ''
    D.reachablePositions 1
  have hb : ∀ y ∈ S, y≤(E.upper:ℝ) := by
    rintro y ⟨w,⟨x,hx,Y,rfl⟩,rfl⟩
    exact E.physical_upper D ha hE he hx Y
  have hm : observable E.normal (PointingCapObstruction.framed (X.p 1))∈S :=
    ⟨X.p 1,⟨fun i => (E.witness i:ℝ),hx,X,rfl⟩,rfl⟩
  have hh := (abs_le.mp (physical_projection_error D ha E.normal hE.1 he hx X)).1
  have hl : (E.lower:ℝ)≤(rationalValue (projection D E.normal) E.witness 1:ℝ)-(ε:ℝ) := by
    exact_mod_cast hE.2.2.2.2.1
  rw [rationalValue_cast,Rat.cast_one] at hl
  exact ⟨(show (E.lower:ℝ)≤observable E.normal (PointingCapObstruction.framed (X.p 1)) by
    linarith).trans (le_csSup ⟨_,hb⟩ hm),csSup_le ⟨_,hm⟩ hb⟩

def polytope {ι : Type*} (entries : ι → Entry) : Set E3 :=
  {z | ∀ i, observable (entries i).normal (PointingCapObstruction.framed z)≤((entries i).upper:ℝ)}

/-- Every physical endpoint belongs to all checked halfspaces simultaneously. -/
theorem reachable_subset_polytope {ι : Type*} (D : Data) (ha : D.alpha=2)
    (entries : ι → Entry) {ε width : ℚ} (h : ∀ i, (entries i).Valid D ε width)
    (he : PhysicalError D ε) : D.reachablePositions 1 ⊆ polytope entries := by
  rintro z ⟨x,hx,X,rfl⟩ i
  exact (entries i).physical_upper D ha (h i) he hx X

end
end GNC.OrbitalComparison.PointingCapPolytope
