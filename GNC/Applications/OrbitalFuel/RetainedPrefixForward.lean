import GNC.Applications.OrbitalFuel.RetainedPrefixTheory

/-! Apply the forward transition once, charging both transition-entry error
and accumulated-forcing error. Rows are Cartesian position then velocity.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPrefix
open GNC GNC.PolynomialODE GNC.PolynomialBounds GNC.Planning.PolynomialKernel
open GNC.PolynomialOrbitTransition PolynomialBurn PolynomialTransition Matrix

def matrixValue (x : Fin 25 → ℝ) (i j : Fin 6) : ℝ :=
  if hi : i.val%3 < 2 then
    if hj : j.val < 4 then x (planeIndex ⟨2*(i.val/3)+i.val%3,by omega⟩ ⟨j.val,hj⟩) else 0
  else if hj : 4 ≤ j.val then x (normalIndex ⟨i.val/3,by omega⟩ ⟨j.val-4,by omega⟩) else 0

set_option maxHeartbeats 2000000 in
theorem forward_evaluation (step : Fin 32) (pulled : Columns) (i : Fin 6) (k : Fin 4) (u : ℝ) :
    evaluate ((forward step pulled i k).map (Rat.castHom ℝ)) u =
      (matrixValue (curve (steps step).coefficients u) *ᵥ
        (fun r => evaluate ((pulled r k).map (Rat.castHom ℝ)) u)) i := by
  unfold forward
  split_ifs with h <;> simp only [add_map, multiply_map, evaluate_add, evaluate_multiply]
  all_goals
    simp [matrixValue, h, curve, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ] <;> ring

theorem matrixValue_bound (x : Fin 25 → ℝ)
    (hx : ∀ j, 5 ≤ j.val → |x j| ≤ 4) (i j : Fin 6) : |matrixValue x i j| ≤ 4 := by
  unfold matrixValue
  split_ifs
  · apply hx
    dsimp only [planeIndex]
    omega
  · norm_num
  · apply hx
    dsimp only [normalIndex]
    omega
  · norm_num

theorem matrixValue_error (x y : Fin 25 → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hxy : ∀ j, 5 ≤ j.val → |x j-y j| ≤ ε) (i j : Fin 6) :
    |matrixValue x i j-matrixValue y i j| ≤ ε := by
  unfold matrixValue
  split_ifs
  · apply hxy
    dsimp only [planeIndex]
    omega
  · simpa only [sub_self,abs_zero] using hε
  · apply hxy
    dsimp only [normalIndex]
    omega
  · simpa only [sub_self,abs_zero] using hε

set_option maxRecDepth 100000 in
theorem transition_regions : ∀ step : Fin 32, ∀ i : Fin 25,
    5 ≤ i.val → (steps step).region i ≤ 4 := by decide +kernel

theorem Data.forward_transfer (d : Data) (p : RetainedNorm.Piece) (hd : d.Valid p)
    (hp : p.Valid) (x : Trajectory) (y : Fin 6 → ℝ) (i : Fin 6) (k : Fin 4) {t ε : ℝ}
    (ht : t ∈ Set.Icc (p.start:ℝ) (p.finish:ℝ))
    (hy : ∀ r, |y r-PolynomialAccumulation.value (d.pulled r k) (p.offset:ℝ) t| ≤ ε) :
    |(matrixValue (x.state t) *ᵥ y) i-
      PolynomialAccumulation.value (output p i k) (p.offset:ℝ) t| ≤
        6*(4*ε+1/10^16)+1/10^18 := by
  let u := t-(p.offset:ℝ)
  let z := curve (steps p.referenceStep).coefficients u
  let v := fun r => PolynomialAccumulation.value (d.pulled r k) (p.offset:ℝ) t
  have hu := p.reference_interval hp ht
  have hx (s : Fin 25) : |x.state t s-z s| ≤ ((steps p.referenceStep).error s:ℝ) := by
    have h := (x.cell_error p.referenceStep hu s).le
    have he : (p.referenceStep.val:ℝ)*(3/160)+(t-(p.offset:ℝ)) = t := by
      simp only [RetainedNorm.Piece.offset, Rat.cast_mul, Rat.cast_natCast,
        Rat.cast_div, Rat.cast_ofNat]
      ring
    simpa only [he] using h
  have hu' : u ∈ Set.Icc (0:ℝ) ((steps p.referenceStep).duration:ℝ) := by
    simp only [durations, Rat.cast_div, Rat.cast_ofNat]
    exact hu
  have hregion (s : Fin 25) (hs : 5 ≤ s.val) : |x.state t s| ≤ 4 := by
    have h := (steps p.referenceStep).actual_box (steps_valid p.referenceStep) hu' (x.state t) hx s
    exact h.trans (by exact_mod_cast transition_regions p.referenceStep s hs)
  have hdiff (s : Fin 25) (hs : 5 ≤ s.val) : |x.state t s-z s| ≤ 1/10^16 := by
    have he := (Rat.cast_lt (K := ℝ)).mpr (transition_error p.referenceStep s hs)
    apply (hx s).trans
    norm_num at he ⊢
    exact he.le
  have hprod (r : Fin 6) :
      |matrixValue (x.state t) i r*y r-matrixValue z i r*v r| ≤ 4*ε+1/10^16 := by
    have ha := matrixValue_bound (x.state t) hregion i r
    have hb := matrixValue_error (x.state t) z (by norm_num : (0:ℝ) ≤ 1/10^16) hdiff i r
    have hv := d.pulled_bound p hd hp r k ht
    have hsplit := abs_add_le (matrixValue (x.state t) i r*(y r-v r))
      ((matrixValue (x.state t) i r-matrixValue z i r)*v r)
    have heq : matrixValue (x.state t) i r*(y r-v r)+
        (matrixValue (x.state t) i r-matrixValue z i r)*v r =
        matrixValue (x.state t) i r*y r-matrixValue z i r*v r := by ring
    rw [heq,abs_mul,abs_mul] at hsplit
    have h1 := mul_le_mul ha (hy r) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
    have h2 := mul_le_mul hb hv (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/10^16)
    change |v r| ≤ 1 at hv
    linarith
  have hsum : |(matrixValue (x.state t) *ᵥ y) i-(matrixValue z *ᵥ v) i| ≤
      6*(4*ε+1/10^16) := by
    simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib]
    have h := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun r (_hr : r ∈ (Finset.univ : Finset (Fin 6))) => hprod r))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using h
  have he := forward_evaluation p.referenceStep d.pulled i k u
  change PolynomialAccumulation.value (forward p.referenceStep d.pulled i k) (p.offset:ℝ) t =
    (matrixValue z *ᵥ v) i at he
  have hf := d.forward_error p hd hp i k ht
  rw [he] at hf
  exact (abs_sub_le _ ((matrixValue z *ᵥ v) i) _).trans (add_le_add hsum hf)

end GNC.Applications.OrbitalFuel.RetainedPrefix
