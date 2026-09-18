import GNC.Dynamics.CartesianRadiusDefect

/-! Bound higher inverse-radius products without expanding their parameter
coefficients. Every omitted product is charged explicitly, including its
known quadratic-in-time growth. This bound concerns the full field. -/
noncomputable section
namespace GNC.SmallOffsetDefect
open Matrix Real

def retained (a d q f : Vec3) (K h : ℝ) : Vec3 :=
  a+K • d+(3*K*h) • q-f

def full (a d q f : Vec3) (K h : ℝ) : Vec3 :=
  a+(K*(1+h)^3) • d+(K*((1+h)^3-1)) • q-f

theorem residual_identity (a d q f : Vec3) (K h : ℝ) :
    full a d q f K h=retained a d q f K h+
      (3*K*h) • d+(K*(3*h^2+h^3)) • (d+q) := by
  ext i
  simp only [full,retained,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem residual_bound (a d q f : Vec3) {K h P H Q R : ℝ}
    (hK : 0≤K) (hd : enorm d≤P) (hh : |h|≤H) (hq : enorm q≤Q)
    (hR : enorm (retained a d q f K h)≤R) :
    enorm (full a d q f K h)≤R+3*K*H*P+K*(3*H^2+H^3)*(P+Q) := by
  have hH := (abs_nonneg h).trans hh
  have hb : |3*h^2+h^3|≤3*H^2+H^3 := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_pow,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<3)]
    gcongr
  have h3 : |3*K*h|≤3*K*H := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤3*K)]
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hK3 : |K*(3*h^2+h^3)|≤K*(3*H^2+H^3) := by
    rw [abs_mul,abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left hb hK
  rw [residual_identity]
  apply (enorm_add_le _ _).trans
  apply add_le_add ((enorm_add_le _ _).trans (add_le_add hR ?_)) ?_
  · rw [enorm_smul]
    exact mul_le_mul h3 hd (enorm_nonneg _) (by positivity)
  · rw [enorm_smul]
    exact mul_le_mul hK3 ((enorm_add_le _ _).trans (add_le_add hd hq))
      (enorm_nonneg _) (by positivity)

theorem residual_growth (a d q f : Vec3) (t : ℝ) {K h P H Q R : ℝ}
    (hK : 0≤K) (hd : enorm d≤P*t^2) (hh : |h|≤H*t^2) (hq : enorm q≤Q)
    (hR : enorm (retained a d q f K h)≤R) :
    enorm (full a d q f K h)≤R+
      (3*K*H*P+3*K*H^2*Q)*t^4+
      (K*H^3*Q+3*K*H^2*P)*t^6+(K*H^3*P)*t^8 := by
  convert residual_bound a d q f hK hd hh hq hR using 1 <;> ring

theorem constraint_bound {r h S H C : ℝ}
    (hr : |r-1|≤S) (hh : |h|≤H) (hc : |r+2*h-1|≤C) :
    |r*(1+h)^2-1|≤C+2*S*H+(1+S)*H^2 := by
  have hS := (abs_nonneg _).trans hr
  have hH := (abs_nonneg _).trans hh
  have hra : |r|≤1+S := by
    have h := abs_add_le (r-1) 1
    norm_num only [sub_add_cancel,abs_one] at h
    linarith
  have he : r*(1+h)^2-1=(r+2*h-1)+2*(r-1)*h+r*h^2 := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add ((abs_add_le _ _).trans (add_le_add hc ?_)) ?_
  · rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num)) hh (abs_nonneg _) (by positivity)
  · rw [abs_mul,abs_pow]
    exact mul_le_mul hra (pow_le_pow_left₀ (abs_nonneg _) hh 2) (by positivity) (by positivity)

theorem constraint_growth (t : ℝ) {r h Q P H C : ℝ}
    (hr : |r-1|≤2*Q*P*t^2+P^2*t^4) (hh : |h|≤H*t^2)
    (hc : |r+2*h-1|≤C) :
    |r*(1+h)^2-1|≤C+
      (4*Q*P*H+H^2)*t^4+(2*P^2*H+2*Q*P*H^2)*t^6+(P^2*H^2)*t^8 := by
  convert constraint_bound hr hh hc using 1 <;> ring

theorem radius_difference_bound (q d : Vec3) {Q P : ℝ}
    (hq : enorm q≤Q) (hd : enorm d≤P) :
    |(1+2*(q ⬝ᵥ d)+enorm d^2)-1|≤2*Q*P+P^2 := by
  have hQ := (enorm_nonneg q).trans hq
  have hP := (enorm_nonneg d).trans hd
  have he : (1+2*(q ⬝ᵥ d)+enorm d^2)-1=2*(q ⬝ᵥ d)+enorm d^2 := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg (sq_nonneg (enorm d))]
  convert add_le_add (mul_le_mul_of_nonneg_left
    ((LieRadiusApproximation.abs_dot_bound _ _).trans
      (mul_le_mul hq hd (enorm_nonneg _) hQ)) (by norm_num : (0:ℝ)≤2))
    (pow_le_pow_left₀ (enorm_nonneg _) hd 2) using 1 <;> ring

theorem radius_difference_growth (q d : Vec3) (t : ℝ) {Q P : ℝ}
    (hq : enorm q≤Q) (hd : enorm d≤P*t^2) :
    |(1+2*(q ⬝ᵥ d)+enorm d^2)-1|≤2*Q*P*t^2+P^2*t^4 := by
  convert radius_difference_bound q d hq hd using 1 <;> ring

end GNC.SmallOffsetDefect
