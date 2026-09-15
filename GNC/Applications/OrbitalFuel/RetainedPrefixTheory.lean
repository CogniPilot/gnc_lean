import GNC.Applications.OrbitalFuel.RetainedPrefixFormula

/-! Soundness of the accumulated-forcing certificates against the actual
validated reference/transition trajectory, rather than a sampled integrand.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPrefix
open GNC GNC.PolynomialODE GNC.PolynomialBounds GNC.Planning.PolynomialKernel
open PolynomialBurn PolynomialTransition

theorem Data.rate_error (d : Data) (p : RetainedNorm.Piece) (hd : d.Valid p)
    (hp : p.Valid) (x : Trajectory) (i : Fin 6) (k : Fin 4) {t : ℝ}
    (ht : t ∈ Set.Icc (p.start:ℝ) (p.finish:ℝ)) :
    |(forcing d.arc i k).value (x.state t)-
      PolynomialAccumulation.rate (d.pulled i k) (p.offset:ℝ) t| ≤ 1/10^14+1/10^18 := by
  have hu := p.reference_interval hp ht
  have hx (j : Fin 25) :
      |x.state t j-curve (steps p.referenceStep).coefficients (t-(p.offset:ℝ)) j| ≤
        ((steps p.referenceStep).error j:ℝ) := by
    have h := (x.cell_error p.referenceStep hu j).le
    have he : (p.referenceStep.val:ℝ)*(3/160)+(t-(p.offset:ℝ)) = t := by
      simp only [RetainedNorm.Piece.offset, Rat.cast_mul, Rat.cast_natCast,
        Rat.cast_div, Rat.cast_ofNat]
      ring
    rwa [he] at h
  have hu' : t-(p.offset:ℝ) ∈ Set.Icc (0:ℝ) ((steps p.referenceStep).duration:ℝ) := by
    rw [durations]; norm_num at hu ⊢; exact hu
  have hob := (steps p.referenceStep).observable_error (steps_valid p.referenceStep)
    hu' (x.state t) hx (forcing d.arc i k)
  have hobs : ((forcing d.arc i k).differenceMajorant (steps p.referenceStep).region
      (steps p.referenceStep).error:ℝ) ≤ 1/10^14 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (hd.2.2 i k).1
    norm_num at h ⊢
    exact h
  have hdef := bound_sound (subtract (differentiate (d.pulled i k))
    ((forcing d.arc i k).coefficients (steps p.referenceStep).coefficients))
    (show |t-(p.offset:ℝ)| ≤ ((3/160:ℚ):ℝ) by
      rw [abs_of_nonneg hu.1]; norm_num; linarith [hu.2])
  simp only [subtract_map, evaluate_subtract] at hdef
  have hbound : (bound (subtract (differentiate (d.pulled i k))
      ((forcing d.arc i k).coefficients (steps p.referenceStep).coefficients)) (3/160):ℝ) ≤
      1/10^18 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (hd.2.2 i k).2.1
    norm_num at h ⊢
    exact h
  have htri := abs_sub_le ((forcing d.arc i k).value (x.state t))
    (evaluate (((forcing d.arc i k).coefficients (steps p.referenceStep).coefficients).map
      (Rat.castHom ℝ)) (t-(p.offset:ℝ)))
    (PolynomialAccumulation.rate (d.pulled i k) (p.offset:ℝ) t)
  change |PolynomialAccumulation.rate (d.pulled i k) (p.offset:ℝ) t-_| ≤ _ at hdef
  rw [abs_sub_comm] at hdef
  linarith

theorem Data.forward_error (d : Data) (p : RetainedNorm.Piece) (hd : d.Valid p)
    (hp : p.Valid) (i : Fin 6) (k : Fin 4) {t : ℝ}
    (ht : t ∈ Set.Icc (p.start:ℝ) (p.finish:ℝ)) :
    |PolynomialAccumulation.value (forward p.referenceStep d.pulled i k) (p.offset:ℝ) t-
      PolynomialAccumulation.value (output p i k) (p.offset:ℝ) t| ≤ 1/10^18 := by
  have hu := p.reference_interval hp ht
  have h := bound_sound (subtract (forward p.referenceStep d.pulled i k) (output p i k))
    (show |t-(p.offset:ℝ)| ≤ ((3/160:ℚ):ℝ) by
      rw [abs_of_nonneg hu.1]; norm_num; linarith [hu.2])
  simp only [subtract_map, evaluate_subtract] at h
  have hb := (Rat.cast_le (K := ℝ)).mpr (hd.2.2 i k).2.2.2
  apply h.trans
  norm_num at hb ⊢
  exact hb

theorem Data.pulled_bound (d : Data) (p : RetainedNorm.Piece) (hd : d.Valid p)
    (hp : p.Valid) (i : Fin 6) (k : Fin 4) {t : ℝ}
    (ht : t ∈ Set.Icc (p.start:ℝ) (p.finish:ℝ)) :
    |PolynomialAccumulation.value (d.pulled i k) (p.offset:ℝ) t| ≤ 1 := by
  have hu := p.reference_interval hp ht
  have h := bound_sound (d.pulled i k)
    (show |t-(p.offset:ℝ)| ≤ ((3/160:ℚ):ℝ) by
      rw [abs_of_nonneg hu.1]; norm_num; linarith [hu.2])
  exact h.trans (by exact_mod_cast (hd.2.2 i k).2.2.1)

theorem Data.jump_error (d e : Data) (p q : RetainedNorm.Piece)
    (h : d.Compatible e p q) (i : Fin 6) (k : Fin 4) :
    |PolynomialAccumulation.value (d.pulled i k) (p.offset:ℝ) (p.finish:ℝ)-
      PolynomialAccumulation.value (e.pulled i k) (q.offset:ℝ) (q.start:ℝ)| ≤ 1/10^18 := by
  have hd := evaluate_map (Rat.castHom ℝ) (d.pulled i k) (p.finish-p.offset)
  have he := evaluate_map (Rat.castHom ℝ) (e.pulled i k) (q.start-q.offset)
  change evaluate ((d.pulled i k).map (Rat.castHom ℝ)) ((p.finish-p.offset:ℚ):ℝ) =
    ((evaluate (d.pulled i k) (p.finish-p.offset):ℚ):ℝ) at hd
  change evaluate ((e.pulled i k).map (Rat.castHom ℝ)) ((q.start-q.offset:ℚ):ℝ) =
    ((evaluate (e.pulled i k) (q.start-q.offset):ℚ):ℝ) at he
  simp only [Rat.cast_sub] at hd he
  unfold PolynomialAccumulation.value
  rw [hd,he]
  have hb := (Rat.cast_le (K := ℝ)).mpr (h.2 i k)
  norm_num at hb ⊢
  exact hb

end GNC.Applications.OrbitalFuel.RetainedPrefix
