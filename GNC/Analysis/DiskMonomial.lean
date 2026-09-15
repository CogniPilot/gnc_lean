import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import GNC.Analysis.BernsteinPolynomial

/-! Bounds retaining a two-dimensional disk instead of independent coordinate
intervals. The scalar power bound reuses mathlib's weighted AM--GM theorem.
The final statements are certificate interfaces: all displayed inequalities
must be proved, rather than supplied as numerical allowances. -/
namespace GNC.DiskMonomial

theorem weighted_power {x y : ℝ} (hx : 0≤x) (hy : 0≤y) (i j : ℕ) :
    x^i*y^j*((i+j:ℕ):ℝ)^(i+j) ≤
      (x+y)^(i+j)*(i:ℝ)^i*(j:ℝ)^j := by
  rcases i with _|i
  · simp only [Nat.zero_add,Nat.cast_zero,pow_zero,one_mul,mul_one]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy (by linarith) _) (by positivity)
  rcases j with _|j
  · simp only [Nat.add_zero,Nat.cast_zero,pow_zero,mul_one]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx (by linarith) _) (by positivity)
  let n : ℝ := (i+1:ℕ)+(j+1:ℕ)
  have hi : (0:ℝ)<(i+1:ℕ) := by positivity
  have hj : (0:ℝ)<(j+1:ℕ) := by positivity
  have hn : 0<n := by dsimp [n]; positivity
  have hncast : (((i+1)+(j+1):ℕ):ℝ)=n := by simp [n]
  have hw : ((i+1:ℕ):ℝ)/n+((j+1:ℕ):ℝ)/n=1 := by
    rw [← add_div]; exact div_self hn.ne'
  have hsum : (((i+1:ℕ):ℝ)/n)*(x/(i+1:ℕ))+
      (((j+1:ℕ):ℝ)/n)*(y/(j+1:ℕ))=(x+y)/n := by
    field_simp
  have hA : 0≤x/(i+1:ℕ) := div_nonneg hx hi.le
  have hB : 0≤y/(j+1:ℕ) := div_nonneg hy hj.le
  have h := Real.geom_mean_le_arith_mean2_weighted
    (div_nonneg hi.le hn.le) (div_nonneg hj.le hn.le) hA hB hw
  rw [hsum] at h
  have hp := pow_le_pow_left₀
    (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)) h ((i+1)+(j+1))
  have hAi : ((x/(i+1:ℕ))^(((i+1:ℕ):ℝ)/n))^((i+1)+(j+1)) =
      (x/(i+1:ℕ))^(i+1) := by
    rw [← Real.rpow_mul_natCast hA,hncast,div_mul_cancel₀ _ hn.ne',Real.rpow_natCast]
  have hBj : ((y/(j+1:ℕ))^(((j+1:ℕ):ℝ)/n))^((i+1)+(j+1)) =
      (y/(j+1:ℕ))^(j+1) := by
    rw [← Real.rpow_mul_natCast hB,hncast,div_mul_cancel₀ _ hn.ne',Real.rpow_natCast]
  rw [mul_pow,hAi,hBj,div_pow,div_pow,div_pow,← mul_div_mul_comm] at hp
  have hfinal := (div_le_div_iff₀
    (mul_pos (pow_pos hi _) (pow_pos hj _)) (pow_pos hn _)).mp hp
  simpa only [hncast,mul_assoc] using hfinal

theorem denominator_positive (i j : ℕ) :
    (0:ℝ)<((i+j:ℕ):ℝ)^(i+j) := by
  by_cases h : i+j=0
  · simp [h]
  · exact pow_pos (by exact_mod_cast Nat.pos_of_ne_zero h) _

/-- An exact scalar check certifies the monomial over the entire disk.
The weighted squared coefficient is i^i j^j / (i+j)^(i+j); the cross-multiplied
form also handles exponent zero without special floating-point conventions. -/
theorem certifies {u v σ b : ℝ} (hb : 0≤b)
    (hcap : u^2+v^2≤σ^2) (i j : ℕ)
    (hcheck : σ^(2*(i+j))*(i:ℝ)^i*(j:ℝ)^j≤b^2*((i+j:ℕ):ℝ)^(i+j)) :
    |u^i*v^j|≤b := by
  have h := weighted_power (sq_nonneg u) (sq_nonneg v) i j
  have hp := pow_le_pow_left₀ (by positivity : 0≤u^2+v^2) hcap (i+j)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (by positivity : (0:ℝ)≤(i:ℝ)^i))
    (by positivity : (0:ℝ)≤(j:ℝ)^j)
  have he : (u^i*v^j)^2=(u^2)^i*(v^2)^j := by
    simp only [mul_pow,← pow_mul,Nat.mul_comm]
  have hh : (u^i*v^j)^2*((i+j:ℕ):ℝ)^(i+j)≤b^2*((i+j:ℕ):ℝ)^(i+j) := by
    rw [he]
    exact h.trans (hm.trans (by simpa only [← pow_mul] using hcheck))
  have hs := le_of_mul_le_mul_right hh (denominator_positive i j)
  nlinarith [sq_abs (u^i*v^j),abs_nonneg (u^i*v^j)]

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal response columns act on a disk with the larger column norm,
instead of the square root of the sum of both squared column norms. -/
theorem orthogonal_pair {a b : E} {u v σ L : ℝ}
    (hσ : 0≤σ) (hL : 0≤L) (hcap : u^2+v^2≤σ^2)
    (ha : ‖a‖≤L) (hb : ‖b‖≤L) (hab : inner ℝ a b=0) :
    ‖u • a+v • b‖≤σ*L := by
  have he : ‖u • a+v • b‖^2=u^2*‖a‖^2+v^2*‖b‖^2 := by
    simp [norm_add_sq_real,inner_smul_left,inner_smul_right,hab,
      norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have ha2 : ‖a‖^2≤L^2 := by nlinarith [norm_nonneg a]
  have hb2 : ‖b‖^2≤L^2 := by nlinarith [norm_nonneg b]
  have h := add_le_add (mul_le_mul_of_nonneg_left ha2 (sq_nonneg u))
    (mul_le_mul_of_nonneg_left hb2 (sq_nonneg v))
  have hh := mul_le_mul_of_nonneg_right hcap (sq_nonneg L)
  have hn : ‖u • a+v • b‖^2≤(σ*L)^2 := by nlinarith
  nlinarith [norm_nonneg (u • a+v • b),mul_nonneg hσ hL]

omit [InnerProductSpace ℝ E] in
/-- A checked scalar squared-norm polynomial bounds a vector curve. The
polynomial identity can be supplied by exact coefficient arithmetic. -/
theorem curve_norm {F : ℝ → E} {p : List ℚ} {B : ℚ}
    (hB : 0≤B) (hcheck : BernsteinPolynomial.checked p 0 1≤B^2)
    (hsquare : ∀ t, ‖F t‖^2=PolynomialOrder.value p t)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖F t‖≤(B:ℝ) := by
  have hp := BernsteinPolynomial.checked_sound p (by norm_num : (0:ℚ)<1)
    (show t ∈ Set.Icc ((0:ℚ):ℝ) ((1:ℚ):ℝ) by simpa using ht)
  have hc : (BernsteinPolynomial.checked p 0 1:ℝ)≤(B:ℝ)^2 := by exact_mod_cast hcheck
  have hb : (0:ℝ)≤B := by exact_mod_cast hB
  have hs : ‖F t‖^2≤(B:ℝ)^2 := by
    rw [hsquare]
    exact (le_abs_self _).trans (hp.trans hc)
  nlinarith [norm_nonneg (F t)]

/-- A disk-linear block and higher monomials form a sound vector enclosure.
The cap, coefficient bounds and scalar monomial checks are explicit; no
independent-coordinate box is substituted for the disk in the linear block. -/
theorem family_bound {ι : Type*} (s : Finset ι) (i j l : ι → ℕ)
    (coeff : ι → E) (b M : ι → ℝ) {a d : E} {u v c σ C L : ℝ}
    (hσ : 0≤σ) (hL : 0≤L) (hcap : u^2+v^2≤σ^2) (hc : |c|≤C)
    (ha : ‖a‖≤L) (hd : ‖d‖≤L) (had : inner ℝ a d=0)
    (hb : ∀ k ∈ s, 0≤b k) (hM : ∀ k ∈ s, ‖coeff k‖≤M k)
    (hcheck : ∀ k ∈ s,
      σ^(2*(i k+j k))*(i k:ℝ)^(i k)*(j k:ℝ)^(j k)≤
        (b k)^2*((i k+j k:ℕ):ℝ)^(i k+j k)) :
    ‖u • a+v • d+∑ k ∈ s, (u^(i k)*v^(j k)*c^(l k)) • coeff k‖≤
      σ*L+∑ k ∈ s, b k*C^(l k)*M k := by
  have hC : 0≤C := (abs_nonneg c).trans hc
  apply (norm_add_le _ _).trans
  apply add_le_add (orthogonal_pair hσ hL hcap ha hd had)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hscalar := certifies (hb k hk) hcap (i k) (j k) (hcheck k hk)
  have hcp : |c|^(l k)≤C^(l k) := pow_le_pow_left₀ (abs_nonneg c) hc _
  have hm := mul_le_mul hscalar hcp (by positivity) (hb k hk)
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_pow]
  exact mul_le_mul hm (hM k hk) (norm_nonneg _)
    (mul_nonneg (hb k hk) (pow_nonneg hC _))
end InnerProduct
end GNC.DiskMonomial
