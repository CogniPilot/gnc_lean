import GNC.Control.QuadraticTube

/-! Quadratic tube closure with an explicitly charged linear propagation defect.
The discriminant is derived, not an arbitrary tolerance. -/
noncomputable section
open Set
namespace GNC.LinearQuadraticTube

def radius (a d b : ℝ) : ℝ := QuadraticTube.radius (a/(1-d)) (b/(1-d))

theorem normalized {a d b : ℝ} (ha : 0<a) (hd : d<1) (hb : 0≤b)
    (hsmall : 4*a*b<(1-d)^2) :
    0<a/(1-d) ∧ 0≤b/(1-d) ∧ 4*(a/(1-d))*(b/(1-d))<1 := by
  have hp : 0<1-d := sub_pos.mpr hd
  refine ⟨div_pos ha hp, div_nonneg hb hp.le, ?_⟩
  have he : 4*(a/(1-d))*(b/(1-d))=4*a*b/(1-d)^2 := by field_simp
  rw [he]
  exact (div_lt_one (sq_pos_of_pos hp)).mpr hsmall

theorem properties {a d b : ℝ} (ha : 0<a) (hd : d<1) (hb : 0≤b)
    (hsmall : 4*a*b<(1-d)^2) :
    a/(1-d)≤radius a d b ∧ radius a d b<2*(a/(1-d)) ∧
      a+d*radius a d b+b*(radius a d b)^2=radius a d b := by
  obtain ⟨ha',hb',hs'⟩ := normalized ha hd hb hsmall
  obtain ⟨hlo,hhi,he⟩ := QuadraticTube.radius_properties ha' hb' hs'
  refine ⟨hlo,hhi,?_⟩
  change a/(1-d)+(b/(1-d))*(radius a d b)^2=radius a d b at he
  have hp : 1-d≠0 := ne_of_gt (sub_pos.mpr hd)
  field_simp at he
  nlinarith

/-- No actual tube bound is assumed. A first-exit argument establishes it. -/
theorem bound {f : ℝ → ℝ} {T a d b : ℝ}
    (hT : 0≤T) (ha : 0<a) (hd0 : 0≤d) (hd : d<1) (hb : 0≤b)
    (hsmall : 4*a*b<(1-d)^2) (hf : Continuous f) (hi : f 0≤a)
    (hn : ∀ t ∈ Icc 0 T, 0≤f t)
    (hr : ∀ R ∈ Icc (0:ℝ) (2*(a/(1-d))), ∀ t ∈ Icc 0 T,
      (∀ s ∈ Icc 0 t, f s≤R) → f t≤a+d*R+b*R^2) :
    ∀ t ∈ Icc 0 T, f t≤radius a d b := by
  obtain ⟨ha',hb',hs'⟩ := normalized ha hd hb hsmall
  have hp : 0<1-d := sub_pos.mpr hd
  have ha_le : a≤a/(1-d) := (le_div_iff₀ hp).mpr (by nlinarith)
  have budget : a+d*(2*(a/(1-d)))+b*(2*(a/(1-d)))^2<2*(a/(1-d)) := by
    have hh : a/(1-d)+(b/(1-d))*(2*(a/(1-d)))^2<2*(a/(1-d)) := by
      nlinarith [mul_lt_mul_of_pos_left hs' ha']
    have hh' := mul_lt_mul_of_pos_right hh hp
    field_simp at hh' ⊢
    nlinarith
  have coarse := IntegralTube.prefix_closure hf
    (hi.trans_lt (ha_le.trans_lt (by linarith)))
    (a := 0) (b := T) (level := 2*(a/(1-d))) (fun t ht hprefix =>
      (hr _ ⟨by positivity, le_rfl⟩ t ht hprefix).trans_lt budget)
  obtain ⟨s,hs,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) hf.continuousOn
  have hresp := hr (f s) ⟨hn s hs,(coarse s hs).le⟩ s hs
    (fun u hu => hm ⟨hu.1,hu.2.trans hs.2⟩)
  obtain ⟨_,hroot,he⟩ := properties ha hd hb hsmall
  have hfactor : 0<1-d-b*(f s+radius a d b) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add (coarse s hs).le hroot.le) hb
    have hdv : 4*b*(a/(1-d))<1-d := by
      rw [show 4*b*(a/(1-d))=4*a*b/(1-d) by ring]
      apply (div_lt_iff₀ hp).mpr
      nlinarith
    nlinarith
  have hmax : f s≤radius a d b := by
    by_contra h
    have := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hfactor
    nlinarith
  exact fun t ht => (hm ht).trans hmax

theorem zero_defect (a b : ℝ) : radius a 0 b=QuadraticTube.radius a b := by
  simp [radius]

theorem closed_form {a d b : ℝ} (hd : d<1) (hsmall : 4*a*b≤(1-d)^2) :
    radius a d b=2*a/((1-d)+Real.sqrt ((1-d)^2-4*a*b)) := by
  have hp : 0<1-d := sub_pos.mpr hd
  have he : 1-4*(a/(1-d))*(b/(1-d))=((1-d)^2-4*a*b)/(1-d)^2 := by
    field_simp
  unfold radius QuadraticTube.radius
  rw [he, Real.sqrt_div (sub_nonneg.mpr hsmall), Real.sqrt_sq_eq_abs, abs_of_pos hp]
  field_simp

/-- Separates first-order numerical error from second-order physical curvature. -/
theorem error_upper {a d b : ℝ} (ha : 0<a) (hd0 : 0≤d) (hd : d<1) (hb : 0≤b)
    (hsmall : 4*a*b<(1-d)^2) :
    d*radius a d b+b*(radius a d b)^2≤
      2*d*(a/(1-d))+4*b*(a/(1-d))^2 := by
  have hp := properties ha hd hb hsmall
  have hpos : 0≤radius a d b := (div_nonneg ha.le (sub_pos.mpr hd).le).trans hp.1
  have h1 := mul_le_mul_of_nonneg_left hp.2.1.le hd0
  have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos hp.2.1.le 2) hb
  nlinarith

end GNC.LinearQuadraticTube
