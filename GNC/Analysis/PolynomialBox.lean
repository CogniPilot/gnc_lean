import GNC.Analysis.PolynomialChain

/-! Componentwise polynomial-ODE certificates. Each state has its own region,
initial error, defect and error allowance. This retains one-way dependence
when a small reference error drives a larger transition-matrix error.
-/
namespace GNC.PolynomialODE
open Planning.PolynomialKernel PolynomialBounds
variable {n : ℕ}

namespace Expr

def boxMajorant (e : Expr n) (M : Fin n → ℚ) : ℚ :=
  match e with
  | constant c => |c|
  | var i => M i
  | add a b => a.boxMajorant M + b.boxMajorant M
  | multiply a b => a.boxMajorant M * b.boxMajorant M
  | negate a => a.boxMajorant M

def differenceMajorant (e : Expr n) (M B : Fin n → ℚ) : ℚ :=
  match e with
  | constant _ => 0
  | var i => B i
  | add a b => a.differenceMajorant M B + b.differenceMajorant M B
  | multiply a b => a.boxMajorant M * b.differenceMajorant M B +
      b.boxMajorant M * a.differenceMajorant M B
  | negate a => a.differenceMajorant M B

theorem boxMajorant_nonneg (e : Expr n) {M : Fin n → ℚ} (hM : ∀ i, 0 ≤ M i) :
    0 ≤ e.boxMajorant M := by
  induction e <;> simp_all [boxMajorant, add_nonneg, mul_nonneg, abs_nonneg]

theorem differenceMajorant_nonneg (e : Expr n) {M B : Fin n → ℚ}
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i) : 0 ≤ e.differenceMajorant M B := by
  induction e with
  | constant c => simp [differenceMajorant]
  | var i => exact hB i
  | add a b ha hb => exact add_nonneg ha hb
  | multiply a b ha hb =>
    exact add_nonneg (mul_nonneg (a.boxMajorant_nonneg hM) hb)
      (mul_nonneg (b.boxMajorant_nonneg hM) ha)
  | negate a ha => exact ha

theorem box_value_bound (e : Expr n) {M : Fin n → ℚ} (hM : ∀ i, 0 ≤ M i)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ (M i : ℝ)) :
    |e.value x| ≤ (e.boxMajorant M : ℝ) := by
  induction e with
  | constant c => simp [value, boxMajorant]
  | var i => exact hx i
  | add a b ha hb =>
    simpa [value, boxMajorant] using
      (abs_add_le (a.value x) (b.value x)).trans (add_le_add ha hb)
  | multiply a b ha hb =>
    simpa [value, boxMajorant, abs_mul] using mul_le_mul ha hb (abs_nonneg _)
      (show (0:ℝ) ≤ (a.boxMajorant M : ℝ) by exact_mod_cast a.boxMajorant_nonneg hM)
  | negate a ha => simpa [value, boxMajorant] using ha

theorem box_difference_bound (e : Expr n) {M B : Fin n → ℚ}
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i) (x y : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ (M i : ℝ)) (hy : ∀ i, |y i| ≤ (M i : ℝ))
    (hxy : ∀ i, |x i-y i| ≤ (B i : ℝ)) :
    |e.value x-e.value y| ≤ (e.differenceMajorant M B : ℝ) := by
  induction e with
  | constant c => simp [value, differenceMajorant]
  | var i => exact hxy i
  | add a b ha hb =>
    have ht := abs_add_le (a.value x-a.value y) (b.value x-b.value y)
    simp only [value, differenceMajorant, Rat.cast_add]
    rw [show a.value x+b.value x-(a.value y+b.value y) =
      (a.value x-a.value y)+(b.value x-b.value y) by ring]
    linarith
  | multiply a b ha hb =>
    have hma : (0:ℝ) ≤ (a.boxMajorant M : ℝ) := by exact_mod_cast a.boxMajorant_nonneg hM
    have hda : (0:ℝ) ≤ (a.differenceMajorant M B : ℝ) := by
      exact_mod_cast a.differenceMajorant_nonneg hM hB
    have h₁ := mul_le_mul (a.box_value_bound hM x hx) hb (abs_nonneg _) hma
    have h₂ := mul_le_mul ha (b.box_value_bound hM y hy) (abs_nonneg _) hda
    have ht := abs_add_le (a.value x*(b.value x-b.value y))
      ((a.value x-a.value y)*b.value y)
    simp only [abs_mul] at ht
    simp only [value, differenceMajorant, Rat.cast_add, Rat.cast_mul]
    rw [show a.value x*b.value x-a.value y*b.value y =
      a.value x*(b.value x-b.value y)+(a.value x-a.value y)*b.value y by ring]
    nlinarith
  | negate a ha =>
    change |-a.value x- -a.value y| ≤ (a.differenceMajorant M B : ℝ)
    rw [show -a.value x- -a.value y = -(a.value x-a.value y) by ring, abs_neg]
    exact ha

end Expr

structure BoxStep (n : ℕ) where
  coefficients : Fin n → List ℚ
  duration : ℚ
  region : Fin n → ℚ
  initialError : Fin n → ℚ
  error : Fin n → ℚ
  defect : Fin n → ℚ

def BoxStep.Valid (s : BoxStep n) (f : Fin n → Expr n) : Prop :=
  0 ≤ s.duration ∧ ∀ i,
    0 ≤ s.region i ∧ 0 ≤ s.initialError i ∧ 0 < s.error i ∧ 0 ≤ s.defect i ∧
    s.initialError i+s.duration*((f i).differenceMajorant s.region s.error+s.defect i) < s.error i ∧
    bound (s.coefficients i) s.duration+s.error i ≤ s.region i ∧
    bound (residual f s.coefficients i) s.duration ≤ s.defect i

instance (s : BoxStep n) (f : Fin n → Expr n) : Decidable (s.Valid f) := by
  unfold BoxStep.Valid
  infer_instance

theorem box_step_sound (s : BoxStep n) (f : Fin n → Expr n) (hs : s.Valid f)
    (x : ℝ → Fin n → ℝ) (hx : Continuous x)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) s.duration,
      HasDerivAt x (fun i => (f i).value (x t)) t)
    (hi : ∀ i, |x 0 i-curve s.coefficients 0 i| ≤ (s.initialError i : ℝ)) :
    ∀ t ∈ Set.Icc (0:ℝ) s.duration, ∀ i,
      |x t i-curve s.coefficients t i| < (s.error i : ℝ) := by
  let p := curve s.coefficients
  let E := fun t i => (x t i-p t i)/(s.error i : ℝ)
  have hB (i) : (0:ℝ) < s.error i := by exact_mod_cast (hs.2 i).2.2.1
  have hM (i) : 0 ≤ s.region i := (hs.2 i).1
  have hBn (i) : 0 ≤ s.error i := (hs.2 i).2.2.1.le
  have hC (i) : (0:ℝ) ≤ (f i).differenceMajorant s.region s.error+s.defect i := by
    exact_mod_cast add_nonneg ((f i).differenceMajorant_nonneg hM hBn) (hs.2 i).2.2.2.1
  have hclose (i) : (s.initialError i:ℝ)+(s.duration:ℝ)*
      ((f i).differenceMajorant s.region s.error+s.defect i) < s.error i := by
    exact_mod_cast (hs.2 i).2.2.2.2.1
  have hT : (0:ℝ) ≤ s.duration := by exact_mod_cast hs.1
  have hp : Continuous p := continuous_iff_continuousAt.mpr
    (fun t => (curve_derivative s.coefficients t).continuousAt)
  have hc : Continuous E := continuous_pi fun i =>
    (((continuous_apply i).comp hx).sub ((continuous_apply i).comp hp)).div_const _
  have hnorm := IntegralTube.prefix_closure (f := fun t => ‖E t‖) hc.norm
    (a := 0) (b := s.duration) (level := 1) (by
      apply (pi_norm_lt_iff (by norm_num : (0:ℝ) < 1)).mpr
      intro i
      simp only [E, Real.norm_eq_abs, abs_div, abs_of_pos (hB i)]
      apply (div_lt_one (hB i)).mpr
      have hei := hi i
      change |x 0 i-p 0 i| ≤ (s.initialError i:ℝ) at hei
      nlinarith [hclose i, mul_nonneg hT (hC i)])
    (fun t ht hprefix => by
      apply (pi_norm_lt_iff (by norm_num : (0:ℝ) < 1)).mpr
      intro i
      have hdiff (u : ℝ) (hu : u ∈ Set.Icc 0 t) :
          |(f i).value (x u)-evaluate
            ((differentiate (s.coefficients i)).map (Rat.castHom ℝ)) u| ≤
          ((f i).differenceMajorant s.region s.error+s.defect i : ℝ) := by
        have hut : |u| ≤ (s.duration:ℝ) := by
          rw [abs_of_nonneg hu.1]; exact hu.2.trans ht.2
        have hpoly (j) : |p u j|+(s.error j:ℝ) ≤ s.region j := by
          have hb := PolynomialBounds.bound_sound (s.coefficients j) hut
          have hr : (bound (s.coefficients j) s.duration:ℝ)+s.error j ≤ s.region j := by
            exact_mod_cast (hs.2 j).2.2.2.2.2.1
          change |p u j| ≤ (bound (s.coefficients j) s.duration:ℝ) at hb
          linarith
        have herr (j) : |x u j-p u j| ≤ (s.error j:ℝ) := by
          have hb := (norm_le_pi_norm (E u) j).trans (hprefix u hu)
          simp only [E, Real.norm_eq_abs, abs_div, abs_of_pos (hB j)] at hb
          exact (div_le_one (hB j)).mp hb
        have hxb (j) : |x u j| ≤ (s.region j:ℝ) := by
          have ha := abs_add_le (x u j-p u j) (p u j)
          simp only [sub_add_cancel] at ha
          linarith [herr j, hpoly j]
        have hlip := (f i).box_difference_bound hM hBn (x u) (p u)
          hxb (fun j => by linarith [hpoly j, hB j]) herr
        have hres := residual_bound f s.coefficients hut i
        have hδ : (bound (residual f s.coefficients i) s.duration:ℝ) ≤ s.defect i := by
          exact_mod_cast (hs.2 i).2.2.2.2.2.2
        have hadd := abs_add_le ((f i).value (x u)-(f i).value (p u))
          ((f i).value (p u)-evaluate
            ((differentiate (s.coefficients i)).map (Rat.castHom ℝ)) u)
        rw [abs_sub_comm] at hres
        change |(f i).value (p u)-_| ≤ _ at hres
        simp only [sub_add_sub_cancel] at hadd
        linarith
      have hm := norm_image_sub_le_of_norm_deriv_le_segment'
        (fun u hu => ((hasDerivAt_pi.mp (hd u ⟨hu.1, hu.2.trans ht.2⟩) i).sub
          (hasDerivAt_pi.mp (curve_derivative s.coefficients u) i)).hasDerivWithinAt)
        (fun u hu => by simpa [Real.norm_eq_abs] using hdiff u (Set.Ico_subset_Icc_self hu))
        t (Set.right_mem_Icc.mpr ht.1)
      simp only [sub_zero, Real.norm_eq_abs] at hm
      have hei := hi i
      simp only [E, Real.norm_eq_abs, abs_div, abs_of_pos (hB i)]
      apply (div_lt_one (hB i)).mpr
      change |x 0 i-p 0 i| ≤ (s.initialError i:ℝ) at hei
      change |(x t i-p t i)-(x 0 i-p 0 i)| ≤ _ at hm
      have ha := abs_sub_abs_le_abs_sub (x t i-p t i) (x 0 i-p 0 i)
      nlinarith [mul_le_mul_of_nonneg_right ht.2 (hC i), hclose i])
  intro t ht i
  have hb := (norm_le_pi_norm (E t) i).trans_lt (hnorm t ht)
  simp only [E, Real.norm_eq_abs, abs_div, abs_of_pos (hB i)] at hb
  exact (div_lt_one (hB i)).mp hb

def BoxStep.Compatible (s next : BoxStep n) : Prop :=
  ∀ i, |evaluate (s.coefficients i) s.duration-evaluate (next.coefficients i) 0|+
    s.error i ≤ next.initialError i

instance (s next : BoxStep n) : Decidable (s.Compatible next) := by
  unfold BoxStep.Compatible
  infer_instance

theorem box_handoff (s next : BoxStep n) (hc : s.Compatible next) (x : Fin n → ℝ)
    (hx : ∀ i, |x i-curve s.coefficients s.duration i| ≤ (s.error i:ℝ)) :
    ∀ i, |x i-curve next.coefficients 0 i| ≤ (next.initialError i:ℝ) := by
  intro i
  have hcast : |curve s.coefficients s.duration i-curve next.coefficients 0 i|+
      (s.error i:ℝ) ≤ next.initialError i := by
    rw [curve_rational, show (0:ℝ) = ((0:ℚ):ℝ) by norm_num, curve_rational]
    exact_mod_cast hc i
  have ha := abs_add_le (x i-curve s.coefficients s.duration i)
    (curve s.coefficients s.duration i-curve next.coefficients 0 i)
  simp only [sub_add_sub_cancel] at ha
  have he := hx i
  linarith

theorem box_chain_sound (S : ℕ → BoxStep n) (f : Fin n → Expr n) (N : ℕ) (h : ℚ)
    (hvalid : ∀ j < N, (S j).Valid f)
    (hduration : ∀ j < N, (S j).duration = h)
    (hjoin : ∀ j, j+1 < N → (S j).Compatible (S (j+1)))
    (x : ℝ → Fin n → ℝ) (hx : Continuous x)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) ((N:ℝ)*h),
      HasDerivAt x (fun i => (f i).value (x t)) t)
    (hi : ∀ i, |x 0 i-curve (S 0).coefficients 0 i| ≤ ((S 0).initialError i:ℝ)) :
    ∀ j < N, ∀ t ∈ Set.Icc (0:ℝ) h, ∀ i,
      |x ((j:ℝ)*h+t) i-curve (S j).coefficients t i| < ((S j).error i:ℝ) := by
  intro j
  induction j with
  | zero =>
    intro hj t ht
    have hh : (0:ℝ) ≤ h := by
      have he := (hvalid 0 hj).1
      rw [hduration 0 hj] at he
      exact_mod_cast he
    have hN : (1:ℝ) ≤ N := by exact_mod_cast hj
    have hb := box_step_sound (S 0) f (hvalid 0 hj) x hx
      (fun u hu => hd u ⟨hu.1, by
        rw [hduration 0 hj] at hu
        nlinarith [mul_nonneg (sub_nonneg.mpr hN) hh, hu.2]⟩) hi t
      (by simpa [hduration 0 hj] using ht)
    simpa using hb
  | succ j ih =>
    intro hj t ht
    have hj' : j < N := Nat.lt_of_succ_lt hj
    have hh : (0:ℝ) ≤ h := by
      have he := (hvalid j hj').1
      rw [hduration j hj'] at he
      exact_mod_cast he
    have hprev := ih hj' (h:ℝ) ⟨hh,le_rfl⟩
    have htime : (j:ℝ)*h+(h:ℝ) = ((j+1:ℕ):ℝ)*h := by push_cast; ring
    rw [htime] at hprev
    have hnext := box_handoff (S j) (S (j+1)) (hjoin j hj)
      (x (((j+1:ℕ):ℝ)*h)) (fun i => by
        simpa [hduration j hj'] using (hprev i).le)
    let shifted := fun u : ℝ => x (((j+1:ℕ):ℝ)*h+u)
    have hshift : Continuous shifted := hx.comp (continuous_const.add continuous_id)
    have hder : ∀ u ∈ Set.Icc (0:ℝ) (S (j+1)).duration,
        HasDerivAt shifted (fun i => (f i).value (shifted u)) u := by
      intro u hu
      rw [hduration (j+1) hj] at hu
      have hjr : ((j+1:ℕ):ℝ)+1 ≤ N := by exact_mod_cast hj
      have hji : (0:ℝ) ≤ ((j+1:ℕ):ℝ) := by positivity
      have hur : ((j+1:ℕ):ℝ)*h+u ∈ Set.Icc (0:ℝ) ((N:ℝ)*h) :=
        ⟨add_nonneg (mul_nonneg hji hh) hu.1,
          by nlinarith [mul_nonneg (sub_nonneg.mpr hjr) hh, hu.2]⟩
      simpa [shifted] using (hd _ hur).scomp u
        ((hasDerivAt_id u).const_add (((j+1:ℕ):ℝ)*h))
    exact box_step_sound (S (j+1)) f (hvalid (j+1) hj) shifted hshift hder
      (by simpa [shifted] using hnext) t (by simpa [hduration (j+1) hj] using ht)

end GNC.PolynomialODE
