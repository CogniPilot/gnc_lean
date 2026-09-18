import GNC.Analysis.DiskMonomial

/-! Sharp monomial budgets over a three-dimensional ball. The certificate
uses a cross-multiplied rational inequality, including zero exponents. It
does not replace the ball by independent coordinate intervals. -/
namespace GNC.BallMonomial

theorem weighted_power {x y z : ℝ} (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
    (i j k : ℕ) :
    x^i*y^j*z^k*((i+j+k:ℕ):ℝ)^(i+j+k) ≤
      (x+y+z)^(i+j+k)*(i:ℝ)^i*(j:ℝ)^j*(k:ℝ)^k := by
  have hxy := DiskMonomial.weighted_power hx hy i j
  have hxyz := DiskMonomial.weighted_power (add_nonneg hx hy) hz (i+j) k
  have h1 := mul_le_mul_of_nonneg_right hxy
    (by positivity : 0≤z^k*((i+j+k:ℕ):ℝ)^(i+j+k))
  have h2 := mul_le_mul_of_nonneg_right hxyz
    (by positivity : 0≤(i:ℝ)^i*(j:ℝ)^j)
  apply (mul_le_mul_iff_left₀ (DiskMonomial.denominator_positive i j)).mp
  calc
    _ = (x^i*y^j*((i+j:ℕ):ℝ)^(i+j))*(z^k*((i+j+k:ℕ):ℝ)^(i+j+k)) := by ring
    _ ≤ ((x+y)^(i+j)*(i:ℝ)^i*(j:ℝ)^j)*(z^k*((i+j+k:ℕ):ℝ)^(i+j+k)) := h1
    _ = ((x+y)^(i+j)*z^k*((i+j+k:ℕ):ℝ)^(i+j+k))*((i:ℝ)^i*(j:ℝ)^j) := by ring
    _ ≤ ((x+y+z)^(i+j+k)*((i+j:ℕ):ℝ)^(i+j)*(k:ℝ)^k)*((i:ℝ)^i*(j:ℝ)^j) := h2
    _ = _ := by ring

theorem certifies {u v w σ b : ℝ} (hb : 0≤b)
    (hcap : u^2+v^2+w^2≤σ^2) (i j k : ℕ)
    (hcheck : σ^(2*(i+j+k))*(i:ℝ)^i*(j:ℝ)^j*(k:ℝ)^k≤
      b^2*((i+j+k:ℕ):ℝ)^(i+j+k)) :
    |u^i*v^j*w^k|≤b := by
  have h := weighted_power (sq_nonneg u) (sq_nonneg v) (sq_nonneg w) i j k
  have hp := pow_le_pow_left₀ (by positivity : 0≤u^2+v^2+w^2) hcap (i+j+k)
  have hm := mul_le_mul_of_nonneg_right hp
    (by positivity : 0≤(i:ℝ)^i*(j:ℝ)^j*(k:ℝ)^k)
  have he : (u^i*v^j*w^k)^2=(u^2)^i*(v^2)^j*(w^2)^k := by
    simp only [mul_pow,←pow_mul,Nat.mul_comm]
  have hh : (u^i*v^j*w^k)^2*((i+j+k:ℕ):ℝ)^(i+j+k)≤
      b^2*((i+j+k:ℕ):ℝ)^(i+j+k) := by
    rw [he]
    apply h.trans
    have hm' : (u^2+v^2+w^2)^(i+j+k)*(i:ℝ)^i*(j:ℝ)^j*(k:ℝ)^k ≤
        σ^(2*(i+j+k))*(i:ℝ)^i*(j:ℝ)^j*(k:ℝ)^k := by
      simpa only [mul_assoc,←pow_mul] using hm
    exact hm'.trans hcheck
  have hs := le_of_mul_le_mul_right hh (DiskMonomial.denominator_positive (i+j) k)
  nlinarith [sq_abs (u^i*v^j*w^k),abs_nonneg (u^i*v^j*w^k)]

end GNC.BallMonomial
