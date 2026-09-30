import GNC.Analysis.MonomialProfileComparison

/-! Input-dependent comparison of the orbital predictor envelopes.

The physical certificates give K = 2 μ θ L / r³, H = μ L²/(r-L)^4,
F = θ² U/2. The geometric and angle-linear envelopes share a certified
gravity Lipschitz gain. They must each pass their own region closure test.
This file compares those sufficient envelopes, not the true errors, and
makes no superiority claim over exact-component Cartesian responses. -/
noncomputable section
namespace GNC.GeometricEnvelopeComparison
open MonomialSupersolution Set

def geometric (K H κ t : ℝ) : ℝ := K*value κ 2 t+4*H*value κ 4 t
def cartesian (F H κ t : ℝ) : ℝ := F*value κ 0 t+3*H*value κ 4 t

/-- With the same response radius and gravity gain, exact Cartesian force
components always have a no-larger ideal envelope. This comparison does not
include the different response representation or query costs. -/
theorem exact_components_le {K H κ t : ℝ} (hK : 0≤K) (hH : 0≤H)
    (hκ : 0≤κ) (hk : κ<56) (ht : 0≤t) :
    cartesian 0 H κ t≤geometric K H κ t := by
  have h2 := mul_nonneg hK (value_nonneg hκ hk ht 2)
  have h4 := mul_nonneg hH (value_nonneg hκ hk ht 4)
  dsimp [cartesian, geometric]
  nlinarith

/-- Retain the onset-time factors in a comparison of the two envelopes. -/
theorem difference_bound {K H F κ t : ℝ} (hK : 0≤K) (hH : 0≤H)
    (hκ : 0≤κ) (hk : κ<56) (ht : 0≤t) :
    geometric K H κ t-cartesian F H κ t ≤
      (K*t^2/6+H*t^4/15-F)*value κ 0 t := by
  have h2 := profile_le_constant hκ hk ht 2
  have h4 := profile_le_constant hκ hk ht 4
  norm_num [pair] at h2 h4
  have hb := add_le_add (mul_le_mul_of_nonneg_left h2 hK)
    (mul_le_mul_of_nonneg_left h4 hH)
  dsimp [geometric, cartesian]
  nlinarith [hb]

/-- A sufficient comparison criterion at any positive normalized time. -/
theorem strict_comparison {K H F κ t : ℝ} (hK : 0≤K) (hH : 0≤H)
    (hκ : 0≤κ) (hk : κ<56) (ht : 0<t)
    (hcriterion : K*t^2/6+H*t^4/15<F) :
    geometric K H κ t<cartesian F H κ t := by
  have h := difference_bound (F := F) hK hH hκ hk ht.le
  have hp := constant_value_pos hκ hk ht
  have hn := mul_neg_of_neg_of_pos (sub_neg.mpr hcriterion) hp
  linarith

/-- One endpoint inequality suffices at every positive time in the burn. -/
theorem uniform_comparison {K H F κ : ℝ} (hK : 0≤K) (hH : 0≤H)
    (hκ : 0≤κ) (hk : κ<56) (hcriterion : K/6+H/15<F) :
    ∀ t ∈ Ioc (0:ℝ) 1, geometric K H κ t<cartesian F H κ t := by
  intro t ht
  apply strict_comparison hK hH hκ hk ht.1
  have h2 := mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1.le ht.2 (n:=2)) hK
  have h4 := mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1.le ht.2 (n:=4)) hH
  nlinarith

/-- Prove a requested envelope ratio q (0 ≤ q ≤ 1), uniformly in time.
The coefficient 4-3q charges the difference of the spatial remainders. -/
theorem uniform_ratio {K H F κ q : ℝ} (hK : 0≤K) (hH : 0≤H)
    (hκ : 0≤κ) (hk : κ<56) (_hq0 : 0≤q) (hq1 : q≤1)
    (hcriterion : K/6+(4-3*q)*H/15<q*F) :
    ∀ t ∈ Ioc (0:ℝ) 1, geometric K H κ t<q*cartesian F H κ t := by
  have hmult : 0≤4-3*q := by linarith
  have h := uniform_comparison hK (mul_nonneg hmult hH) hκ hk hcriterion
  intro t ht
  have hc := h t ht
  dsimp [geometric, cartesian] at hc ⊢
  nlinarith

/-- Gravity-weighted criterion in physical parameters (using normalized time).
B is the response gain in L=θ U B. This expression is dimensionless. -/
def criterion (μ r θ U B : ℝ) : ℝ :=
  2*μ*B/(3*r^3)+2*μ*U*B^2/(15*(r-θ*U*B)^4)

theorem physical_identity {μ r θ U B : ℝ} (hr : r≠0) (hd : r-θ*U*B≠0) :
    (2*μ*θ*(θ*U*B)/r^3)/6+(μ*(θ*U*B)^2/(r-θ*U*B)^4)/15 =
      (θ^2*U/2)*criterion μ r θ U B := by
  unfold criterion
  field_simp
  ring

/-- Small dimensionless gravity coupling gives a strict envelope advantage.
Physical applicability also requires the two prediction certificates' closures. -/
theorem physical_comparison {μ r θ U B κ : ℝ}
    (hμ : 0≤μ) (hr : 0<r) (hθ : 0<θ) (hU : 0<U) (hB : 0≤B)
    (hd : θ*U*B<r) (hκ : 0≤κ) (hk : κ<56)
    (hcriterion : criterion μ r θ U B<1) :
    ∀ t ∈ Ioc (0:ℝ) 1,
      geometric (2*μ*θ*(θ*U*B)/r^3) (μ*(θ*U*B)^2/(r-θ*U*B)^4) κ t <
      cartesian (θ^2*U/2) (μ*(θ*U*B)^2/(r-θ*U*B)^4) κ t := by
  apply uniform_comparison (by positivity) (by positivity) hκ hk
  rw [physical_identity hr.ne' (sub_pos.mpr hd).ne']
  have hp : 0<θ^2*U/2 := by positivity
  simpa using mul_lt_mul_of_pos_left hcriterion hp

end GNC.GeometricEnvelopeComparison
