import GNC.Analysis.InitialSecondOrderCertificate
import GNC.Analysis.PolynomialSupersolution

/-! Explicit polynomial envelopes on normalized time `[0,1]` for a
second-order error certificate with nonzero initial radii. A cosine-like
polynomial carries the initial position radius, a sine-like polynomial the
initial velocity radius, and the unit-forcing supersolution of
`PolynomialSupersolution` the forcing bound. Each truncated series is closed
by a single final monomial whose coefficient makes the residual of the
comparison inequality a nonnegative polynomial on `[0,1]`; the thresholds
`56 = 8*7` and `72 = 9*8` are the second-derivative coefficients of those
final monomials. The combined envelope is applied to one step of physical
length `T` and composed over a chain of steps with handoff mismatches. -/
noncomputable section
namespace GNC.InitialPolynomialSupersolution
open Set

/-! ## Cosine-like polynomial: `c'' ≥ k c`, `c 0 = 1`, `c' 0 = 0`. -/

def c (k τ : ℝ) : ℝ :=
  1+k/2*τ^2+k^2/24*τ^4+k^3/720*τ^6+k^4/(720*(56-k))*τ^8

def cv (k τ : ℝ) : ℝ :=
  k*τ+k^2/6*τ^3+k^3/120*τ^5+k^4/(90*(56-k))*τ^7

def cw (k τ : ℝ) : ℝ :=
  k+k^2/2*τ^2+k^3/24*τ^4+7*k^4/(90*(56-k))*τ^6

theorem c_hasDerivAt (k τ : ℝ) : HasDerivAt (c k) (cv k τ) τ := by
  have h := ((((hasDerivAt_const τ (1:ℝ)).add
    ((hasDerivAt_pow 2 τ).const_mul (k/2))).add
    ((hasDerivAt_pow 4 τ).const_mul (k^2/24))).add
    ((hasDerivAt_pow 6 τ).const_mul (k^3/720))).add
    ((hasDerivAt_pow 8 τ).const_mul (k^4/(720*(56-k))))
  refine h.congr_deriv ?_
  unfold cv
  simp only [div_eq_mul_inv,mul_inv,Nat.cast_ofNat,Nat.reduceSub]
  ring

theorem cv_hasDerivAt (k τ : ℝ) : HasDerivAt (cv k) (cw k τ) τ := by
  have h := ((((hasDerivAt_id' (x := τ)).const_mul k).add
    ((hasDerivAt_pow 3 τ).const_mul (k^2/6))).add
    ((hasDerivAt_pow 5 τ).const_mul (k^3/120))).add
    ((hasDerivAt_pow 7 τ).const_mul (k^4/(90*(56-k))))
  refine h.congr_deriv ?_
  unfold cw
  simp only [div_eq_mul_inv,mul_inv,Nat.cast_ofNat,Nat.reduceSub]
  ring

theorem c_zero (k : ℝ) : c k 0 = 1 := by simp [c]

theorem cv_zero (k : ℝ) : cv k 0 = 0 := by simp [cv]

theorem c_defect_identity {k : ℝ} (hk : k < 56) (τ : ℝ) :
    cw k τ-k*c k τ = k^5*τ^6*(1-τ^2)/(720*(56-k)) := by
  have hd : (56:ℝ)-k ≠ 0 := ne_of_gt (sub_pos.mpr hk)
  unfold cw c
  field_simp
  ring

theorem c_supersolution {k τ : ℝ} (hk0 : 0 ≤ k) (hk : k < 56)
    (ht : τ ∈ Icc (0:ℝ) 1) : k*c k τ ≤ cw k τ := by
  have h := c_defect_identity hk τ
  have ht2 : 0 ≤ 1-τ^2 := sub_nonneg.mpr (pow_le_one₀ ht.1 ht.2)
  have hd : 0 < (56:ℝ)-k := sub_pos.mpr hk
  have hn : 0 ≤ k^5*τ^6*(1-τ^2)/(720*(56-k)) := by positivity
  linarith

theorem c_bounds {k τ : ℝ} (hk0 : 0 ≤ k) (hk : k < 56)
    (ht : τ ∈ Icc (0:ℝ) 1) :
    0 ≤ c k τ ∧ c k τ ≤ c k 1 ∧ 0 ≤ cv k τ ∧ cv k τ ≤ cv k 1 := by
  have hd : 0 < (56:ℝ)-k := sub_pos.mpr hk
  have ht0 := ht.1
  unfold c cv
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · gcongr <;> first | exact ht.1 | exact ht.2
  · gcongr <;> first | exact ht.1 | exact ht.2

/-! ## Sine-like polynomial: `s'' ≥ k s`, `s 0 = 0`, `s' 0 = 1`. -/

def s (k τ : ℝ) : ℝ :=
  τ+k/6*τ^3+k^2/120*τ^5+k^3/5040*τ^7+k^4/(5040*(72-k))*τ^9

def sv (k τ : ℝ) : ℝ :=
  1+k/2*τ^2+k^2/24*τ^4+k^3/720*τ^6+k^4/(560*(72-k))*τ^8

def sw (k τ : ℝ) : ℝ :=
  k*τ+k^2/6*τ^3+k^3/120*τ^5+k^4/(70*(72-k))*τ^7

theorem s_hasDerivAt (k τ : ℝ) : HasDerivAt (s k) (sv k τ) τ := by
  have h := ((((hasDerivAt_id' (x := τ)).add
    ((hasDerivAt_pow 3 τ).const_mul (k/6))).add
    ((hasDerivAt_pow 5 τ).const_mul (k^2/120))).add
    ((hasDerivAt_pow 7 τ).const_mul (k^3/5040))).add
    ((hasDerivAt_pow 9 τ).const_mul (k^4/(5040*(72-k))))
  refine h.congr_deriv ?_
  unfold sv
  simp only [div_eq_mul_inv,mul_inv,Nat.cast_ofNat,Nat.reduceSub]
  ring

theorem sv_hasDerivAt (k τ : ℝ) : HasDerivAt (sv k) (sw k τ) τ := by
  have h := ((((hasDerivAt_const τ (1:ℝ)).add
    ((hasDerivAt_pow 2 τ).const_mul (k/2))).add
    ((hasDerivAt_pow 4 τ).const_mul (k^2/24))).add
    ((hasDerivAt_pow 6 τ).const_mul (k^3/720))).add
    ((hasDerivAt_pow 8 τ).const_mul (k^4/(560*(72-k))))
  refine h.congr_deriv ?_
  unfold sw
  simp only [div_eq_mul_inv,mul_inv,Nat.cast_ofNat,Nat.reduceSub]
  ring

theorem s_zero (k : ℝ) : s k 0 = 0 := by simp [s]

theorem sv_zero (k : ℝ) : sv k 0 = 1 := by simp [sv]

theorem s_defect_identity {k : ℝ} (hk : k < 72) (τ : ℝ) :
    sw k τ-k*s k τ = k^5*τ^7*(1-τ^2)/(5040*(72-k)) := by
  have hd : (72:ℝ)-k ≠ 0 := ne_of_gt (sub_pos.mpr hk)
  unfold sw s
  field_simp
  ring

theorem s_supersolution {k τ : ℝ} (hk0 : 0 ≤ k) (hk : k < 72)
    (ht : τ ∈ Icc (0:ℝ) 1) : k*s k τ ≤ sw k τ := by
  have h := s_defect_identity hk τ
  have ht2 : 0 ≤ 1-τ^2 := sub_nonneg.mpr (pow_le_one₀ ht.1 ht.2)
  have hd : 0 < (72:ℝ)-k := sub_pos.mpr hk
  have ht0 := ht.1
  have hn : 0 ≤ k^5*τ^7*(1-τ^2)/(5040*(72-k)) := by positivity
  linarith

theorem s_bounds {k τ : ℝ} (hk0 : 0 ≤ k) (hk : k < 72)
    (ht : τ ∈ Icc (0:ℝ) 1) :
    0 ≤ s k τ ∧ s k τ ≤ s k 1 ∧ 0 ≤ sv k τ ∧ sv k τ ≤ sv k 1 := by
  have hd : 0 < (72:ℝ)-k := sub_pos.mpr hk
  have ht0 := ht.1
  unfold s sv
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · gcongr <;> first | exact ht.1 | exact ht.2
  · gcongr <;> first | exact ht.1 | exact ht.2

/-! ## Combined envelope on normalized time. -/

/-- `rp` initial position radius, `rv` initial velocity radius (normalized
time), `F` forcing bound (normalized time), `k` the normalized stiffness. -/
def envelope (k rp rv F τ : ℝ) : ℝ :=
  rp*c k τ+rv*s k τ+F*PolynomialSupersolution.value k τ

def envelopeVelocity (k rp rv F τ : ℝ) : ℝ :=
  rp*cv k τ+rv*sv k τ+F*PolynomialSupersolution.velocity k τ

def envelopeAcceleration (k rp rv F τ : ℝ) : ℝ :=
  rp*cw k τ+rv*sw k τ+F*PolynomialSupersolution.acceleration k τ

theorem envelope_hasDerivAt (k rp rv F τ : ℝ) :
    HasDerivAt (envelope k rp rv F) (envelopeVelocity k rp rv F τ) τ :=
  (((c_hasDerivAt k τ).const_mul rp).add ((s_hasDerivAt k τ).const_mul rv)).add
    ((PolynomialSupersolution.derivative k τ).const_mul F)

theorem envelopeVelocity_hasDerivAt (k rp rv F τ : ℝ) :
    HasDerivAt (envelopeVelocity k rp rv F) (envelopeAcceleration k rp rv F τ) τ :=
  (((cv_hasDerivAt k τ).const_mul rp).add ((sv_hasDerivAt k τ).const_mul rv)).add
    ((PolynomialSupersolution.velocity_derivative k τ).const_mul F)

theorem envelope_zero (k rp rv F : ℝ) : envelope k rp rv F 0 = rp := by
  simp [envelope,c_zero,s_zero,(PolynomialSupersolution.initial k).1]

theorem envelopeVelocity_zero (k rp rv F : ℝ) : envelopeVelocity k rp rv F 0 = rv := by
  simp [envelopeVelocity,cv_zero,sv_zero,(PolynomialSupersolution.initial k).2]

theorem envelope_supersolution {k rp rv F τ : ℝ} (hrp : 0 ≤ rp) (hrv : 0 ≤ rv)
    (hF : 0 ≤ F) (hk0 : 0 ≤ k) (hk : k < 56) (ht : τ ∈ Icc (0:ℝ) 1) :
    k*envelope k rp rv F τ+F ≤ envelopeAcceleration k rp rv F τ := by
  have hc := mul_le_mul_of_nonneg_left (c_supersolution hk0 hk ht) hrp
  have hs := mul_le_mul_of_nonneg_left (s_supersolution hk0 (by linarith) ht) hrv
  have hh := mul_le_mul_of_nonneg_left (PolynomialSupersolution.supersolution hk ht) hF
  unfold envelope envelopeAcceleration
  nlinarith

theorem envelope_bounds {k rp rv F τ : ℝ} (hrp : 0 ≤ rp) (hrv : 0 ≤ rv)
    (hF : 0 ≤ F) (hk0 : 0 ≤ k) (hk : k < 56) (ht : τ ∈ Icc (0:ℝ) 1) :
    0 ≤ envelope k rp rv F τ ∧ envelope k rp rv F τ ≤ envelope k rp rv F 1 ∧
      0 ≤ envelopeVelocity k rp rv F τ ∧
        envelopeVelocity k rp rv F τ ≤ envelopeVelocity k rp rv F 1 := by
  obtain ⟨c0,c1,cv0,cv1⟩ := c_bounds hk0 hk ht
  obtain ⟨s0,s1,sv0,sv1⟩ := s_bounds hk0 (by linarith) ht
  obtain ⟨h0,h1,hv0,hv1⟩ := PolynomialSupersolution.bounds hk0 hk ht
  unfold envelope envelopeVelocity
  exact ⟨add_nonneg (add_nonneg (mul_nonneg hrp c0) (mul_nonneg hrv s0)) (mul_nonneg hF h0),
    add_le_add (add_le_add (mul_le_mul_of_nonneg_left c1 hrp)
      (mul_le_mul_of_nonneg_left s1 hrv)) (mul_le_mul_of_nonneg_left h1 hF),
    add_nonneg (add_nonneg (mul_nonneg hrp cv0) (mul_nonneg hrv sv0)) (mul_nonneg hF hv0),
    add_le_add (add_le_add (mul_le_mul_of_nonneg_left cv1 hrp)
      (mul_le_mul_of_nonneg_left sv1 hrv)) (mul_le_mul_of_nonneg_left hv1 hF)⟩

/-! ## One step of physical length `T`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The error curve `p` with velocity `v` and acceleration `acc` on `[0,T]`,
whose acceleration is bounded by `κ‖p‖+f` inside the tube of radius `M`, is
enclosed by the normalized envelope with stiffness `T^2 κ`, velocity radius
`T rv` and forcing `T^2 F`, evaluated at `t/T`. -/
theorem step_envelope (p v acc : ℝ → E) (f : ℝ → ℝ) {T κ F rp rv M : ℝ}
    (hT : 0 < T) (hκ : 0 ≤ κ) (hF : 0 ≤ F) (hk : T^2*κ < 56)
    (hclose : envelope (T^2*κ) rp (T*rv) (T^2*F) 1 < M)
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc 0 T, HasDerivAt v (acc t) t)
    (hip : ‖p 0‖ ≤ rp) (hiv : ‖v 0‖ ≤ rv)
    (hf : ∀ t ∈ Icc 0 T, f t ≤ F)
    (ha : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ M → ‖acc t‖ ≤ κ*‖p t‖+f t) :
    ∀ t ∈ Icc 0 T, ‖p t‖ ≤ envelope (T^2*κ) rp (T*rv) (T^2*F) (t/T) ∧
      ‖v t‖ ≤ envelopeVelocity (T^2*κ) rp (T*rv) (T^2*F) (t/T)/T := by
  have hk0 : 0 ≤ T^2*κ := by positivity
  have hrp : 0 ≤ rp := (norm_nonneg _).trans hip
  have hrv : 0 ≤ T*rv := mul_nonneg hT.le ((norm_nonneg _).trans hiv)
  have hF' : 0 ≤ T^2*F := by positivity
  have hT0 : T ≠ 0 := hT.ne'
  have hmem : ∀ t ∈ Icc 0 T, t/T ∈ Icc (0:ℝ) 1 := fun t ht =>
    ⟨div_nonneg ht.1 hT.le,(div_le_one hT).mpr ht.2⟩
  have hB := (PolynomialSupersolution.bounds hk0 hk (right_mem_Icc.mpr zero_le_one)).1
  have hBV := (PolynomialSupersolution.bounds hk0 hk (right_mem_Icc.mpr zero_le_one)).2.2.1
  have hscale : ∀ t : ℝ, HasDerivAt (fun x : ℝ => x/T) (1/T) t :=
    fun t => (hasDerivAt_id' t).div_const T
  have hP : ∀ t, HasDerivAt (fun t => envelope (T^2*κ) rp (T*rv) (T^2*F) (t/T))
      (envelopeVelocity (T^2*κ) rp (T*rv) (T^2*F) (t/T)/T) t := by
    intro t
    have h := (envelope_hasDerivAt (T^2*κ) rp (T*rv) (T^2*F) (t/T)).comp t (hscale t)
    exact h.congr_deriv (by ring)
  have hV : ∀ t, HasDerivAt (fun t => envelopeVelocity (T^2*κ) rp (T*rv) (T^2*F) (t/T)/T)
      (envelopeAcceleration (T^2*κ) rp (T*rv) (T^2*F) (t/T)/T^2) t := by
    intro t
    have h := ((envelopeVelocity_hasDerivAt (T^2*κ) rp (T*rv) (T^2*F) (t/T)).comp t
      (hscale t)).div_const T
    exact h.congr_deriv (by ring)
  have hb : ∀ t, HasDerivAt (fun t => T^2*PolynomialSupersolution.value (T^2*κ) (t/T))
      (T*PolynomialSupersolution.velocity (T^2*κ) (t/T)) t := by
    intro t
    have h := ((PolynomialSupersolution.derivative (T^2*κ) (t/T)).comp t
      (hscale t)).const_mul (T^2)
    exact h.congr_deriv (by field_simp)
  have hbv : ∀ t, HasDerivAt (fun t => T*PolynomialSupersolution.velocity (T^2*κ) (t/T))
      (PolynomialSupersolution.acceleration (T^2*κ) (t/T)) t := by
    intro t
    have h := ((PolynomialSupersolution.velocity_derivative (T^2*κ) (t/T)).comp t
      (hscale t)).const_mul T
    exact h.congr_deriv (by field_simp)
  exact SecondOrderCertificate.regional_initial_response p v acc f
    (fun t => envelope (T^2*κ) rp (T*rv) (T^2*F) (t/T))
    (fun t => envelopeVelocity (T^2*κ) rp (T*rv) (T^2*F) (t/T)/T)
    (fun t => envelopeAcceleration (T^2*κ) rp (T*rv) (T^2*F) (t/T)/T^2)
    (fun t => T^2*PolynomialSupersolution.value (T^2*κ) (t/T))
    (fun t => T*PolynomialSupersolution.velocity (T^2*κ) (t/T))
    (fun t => PolynomialSupersolution.acceleration (T^2*κ) (t/T))
    (T := T) (κ := κ) (B := T^2*PolynomialSupersolution.value (T^2*κ) 1)
    (BV := T*PolynomialSupersolution.velocity (T^2*κ) 1) (M := M)
    hT.le hκ (by positivity) (by positivity)
    (fun t ht => (envelope_bounds hrp hrv hF' hk0 hk (hmem t ht)).2.1.trans_lt hclose)
    hp hv hdp hdv hP hV hb hbv
    (by show ‖p 0‖ ≤ envelope (T^2*κ) rp (T*rv) (T^2*F) (0/T)
        rw [zero_div,envelope_zero]; exact hip)
    (by show ‖v 0‖ ≤ envelopeVelocity (T^2*κ) rp (T*rv) (T^2*F) (0/T)/T
        rw [zero_div,envelopeVelocity_zero,mul_div_cancel_left₀ rv hT0]; exact hiv)
    (by show T^2*PolynomialSupersolution.value (T^2*κ) (0/T) = 0
        rw [zero_div,(PolynomialSupersolution.initial _).1,mul_zero])
    (by show T*PolynomialSupersolution.velocity (T^2*κ) (0/T) = 0
        rw [zero_div,(PolynomialSupersolution.initial _).2,mul_zero])
    (by intro t ht
        have h := PolynomialSupersolution.supersolution hk (hmem t ht)
        linarith)
    (by intro t ht
        have h := PolynomialSupersolution.bounds hk0 hk (hmem t ht)
        exact ⟨mul_le_mul_of_nonneg_left h.2.1 (by positivity),
          mul_le_mul_of_nonneg_left h.2.2.2 hT.le⟩)
    (by intro t ht
        rw [le_div_iff₀ (by positivity)]
        have h := envelope_supersolution hrp hrv hF' hk0 hk (hmem t ht)
        have hf' := mul_le_mul_of_nonneg_left (hf t ht) (sq_nonneg T)
        linarith)
    ha

/-! ## Composition over a chain of steps. -/

/-- Steps `j < N` of lengths `T j` with error curves `p j`, `v j`, `acc j`.
The initial radii of step `j+1` dominate the terminal envelope of step `j`
plus the handoff mismatch between the two reference curves. -/
theorem chain_envelope {N : ℕ} (T κ F rp rv M d e : ℕ → ℝ)
    (p v acc : ℕ → ℝ → E) (f : ℕ → ℝ → ℝ)
    (hT : ∀ j < N, 0 < T j) (hκ : ∀ j < N, 0 ≤ κ j) (hF : ∀ j < N, 0 ≤ F j)
    (hk : ∀ j < N, (T j)^2*κ j < 56)
    (hclose : ∀ j < N, envelope ((T j)^2*κ j) (rp j) (T j*rv j) ((T j)^2*F j) 1 < M j)
    (hp : ∀ j < N, Continuous (p j)) (hv : ∀ j < N, Continuous (v j))
    (hdp : ∀ j < N, ∀ t ∈ Icc 0 (T j), HasDerivAt (p j) (v j t) t)
    (hdv : ∀ j < N, ∀ t ∈ Icc 0 (T j), HasDerivAt (v j) (acc j t) t)
    (hf : ∀ j < N, ∀ t ∈ Icc 0 (T j), f j t ≤ F j)
    (ha : ∀ j < N, ∀ t ∈ Icc 0 (T j), ‖p j t‖ ≤ M j →
      ‖acc j t‖ ≤ κ j*‖p j t‖+f j t)
    (hip : ‖p 0 0‖ ≤ rp 0) (hiv : ‖v 0 0‖ ≤ rv 0)
    (hd : ∀ j, j+1 < N → ‖p (j+1) 0-p j (T j)‖ ≤ d j)
    (he : ∀ j, j+1 < N → ‖v (j+1) 0-v j (T j)‖ ≤ e j)
    (hrp : ∀ j, j+1 < N →
      envelope ((T j)^2*κ j) (rp j) (T j*rv j) ((T j)^2*F j) 1+d j ≤ rp (j+1))
    (hrv : ∀ j, j+1 < N →
      envelopeVelocity ((T j)^2*κ j) (rp j) (T j*rv j) ((T j)^2*F j) 1/T j+e j ≤ rv (j+1)) :
    ∀ j < N, ∀ t ∈ Icc 0 (T j),
      ‖p j t‖ ≤ envelope ((T j)^2*κ j) (rp j) (T j*rv j) ((T j)^2*F j) (t/T j) ∧
        ‖v j t‖ ≤ envelopeVelocity ((T j)^2*κ j) (rp j) (T j*rv j) ((T j)^2*F j) (t/T j)/T j := by
  have key : ∀ j < N, ‖p j 0‖ ≤ rp j ∧ ‖v j 0‖ ≤ rv j := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨hip,hiv⟩
    | succ j ih =>
      intro hj
      have hjN : j < N := by omega
      obtain ⟨h1,h2⟩ := ih hjN
      have hstep := step_envelope (p j) (v j) (acc j) (f j) (hT j hjN) (hκ j hjN) (hF j hjN)
        (hk j hjN) (hclose j hjN) (hp j hjN) (hv j hjN) (hdp j hjN) (hdv j hjN) h1 h2
        (hf j hjN) (ha j hjN) (T j) ⟨(hT j hjN).le,le_rfl⟩
      rw [div_self (hT j hjN).ne'] at hstep
      constructor
      · calc ‖p (j+1) 0‖ = ‖(p (j+1) 0-p j (T j))+p j (T j)‖ := by rw [sub_add_cancel]
          _ ≤ ‖p (j+1) 0-p j (T j)‖+‖p j (T j)‖ := norm_add_le _ _
          _ ≤ rp (j+1) := by linarith [hd j hj,hstep.1,hrp j hj]
      · calc ‖v (j+1) 0‖ = ‖(v (j+1) 0-v j (T j))+v j (T j)‖ := by rw [sub_add_cancel]
          _ ≤ ‖v (j+1) 0-v j (T j)‖+‖v j (T j)‖ := norm_add_le _ _
          _ ≤ rv (j+1) := by linarith [he j hj,hstep.2,hrv j hj]
  intro j hj
  exact step_envelope (p j) (v j) (acc j) (f j) (hT j hj) (hκ j hj) (hF j hj)
    (hk j hj) (hclose j hj) (hp j hj) (hv j hj) (hdp j hj) (hdv j hj)
    (key j hj).1 (key j hj).2 (hf j hj) (ha j hj)

end GNC.InitialPolynomialSupersolution
