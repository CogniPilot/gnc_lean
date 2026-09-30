import GNC.Dynamics.GeometricSTMDefect
import GNC.Dynamics.MonomialOrbitCertificate
import GNC.Dynamics.RetainedMonomialCertificate
import GNC.Applications.OrbitalComparison.LieRadiusFrame

/-! From a geometric angle-STM predictor to a physical orbital certificate.
The reference and linear response solve their defining equations exactly;
the numerical-candidate defect theorem is available separately. All three
components of the fixed inertial attitude offset are allowed. -/
noncomputable section
namespace GNC.OrbitalComparison.GeometricSTMPrediction
open Set Matrix Real
open LieRadiusFrame (left left_derivative left_norm)
abbrev E := Jacobian.E3

def cross (φ : Vec3) (u : E) : E := WithLp.toLp 2 (φ ⨯₃ u.ofLp)
def force (φ : Vec3) (u : E) : E := WithLp.toLp 2 (rotate (rotationExp φ) u.ofLp)

/-- A bound on the *known linear response*, independent of an unknown
physical trajectory. This also supplies the complete time profile. -/
theorem response_shape (μ r θ U : ℝ) (hμ : 0≤μ) (hr : 0<r)
    (hθ : 0≤θ) (hU : 0≤U) (hk : 2*μ/r^3<56) (φ : Vec3)
    (hφ : enorm φ≤θ) (q y yv u : ℝ → E)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r≤‖q t‖)
    (hu : ∀ t ∈ Icc (0:ℝ) 1, ‖u t‖≤U)
    (hy : Continuous y) (hyv : Continuous yv)
    (hdy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt y (yv t) t)
    (hdyv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt yv (Gravity.gradient μ (q t) (y t)+cross φ (u t)) t)
    (hi : y 0=0) (hiv : yv 0=0) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖y t‖≤(θ*U*PolynomialSupersolution.value (2*μ/r^3) 1)*t^2 := by
  exact Gravity.retained_response_shape μ r (θ*U) hμ hr (mul_nonneg hθ hU) hk q y yv
    (fun t => cross φ (u t)) hq (fun t ht => (cross_enorm_le φ (u t).ofLp).trans
      (mul_le_mul hφ (hu t ht) (norm_nonneg _) hθ)) hy hyv hdy hdyv hi hiv

/-- Full nonlinear physical trajectory containment about the geometric
candidate. The known reference stays outside r, and L bounds its retained
response. A coarse first-exit check closes radius L; the final bound keeps
the t^2 and t^4 source profiles. -/
theorem certificate (μ r L θ κ : ℝ) (hμ : 0≤μ) (hr : 0<r)
    (hL : 0≤L) (hregion : 2*L<r) (hθ : 0≤θ) (hθ1 : θ≤1)
    (hκ : 0≤κ) (hk : κ<56) (hlip : 2*μ/(r-2*L)^3≤κ)
    (hclose : (2*μ/r^3*θ*L+4*μ/(r-L)^4*L^2)*
      PolynomialSupersolution.value κ 1<L)
    (φ : Vec3) (hφ : enorm φ≤θ) (x xv q qv y yv u : ℝ → E)
    (hq : ∀ t ∈ Icc (0:ℝ) 1, r≤‖q t‖)
    (hybound : ∀ t ∈ Icc (0:ℝ) 1, ‖y t‖≤L*t^2)
    (hx : Continuous x) (hxv : Continuous xv)
    (hcq : Continuous q) (hcqv : Continuous qv)
    (hy : Continuous y) (hyv : Continuous yv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdxv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt xv (Gravity.field μ (x t)+force φ (u t)) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (Gravity.field μ (q t)+u t) t)
    (hdy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt y (yv t) t)
    (hdyv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt yv (Gravity.gradient μ (q t) (y t)+cross φ (u t)) t)
    (hip : x 0=q 0+left φ (y 0)) (hiv : xv 0=qv 0+left φ (yv 0)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖x t-(q t+left φ (y t))‖≤
        (2*μ/r^3*θ*L)*MonomialSupersolution.value κ 2 t+
        (4*μ/(r-L)^4*L^2)*MonomialSupersolution.value κ 4 t ∧
      ‖xv t-(qv t+left φ (yv t))‖≤
        (2*μ/r^3*θ*L)*MonomialSupersolution.velocity κ 2 t+
        (4*μ/(r-L)^4*L^2)*MonomialSupersolution.velocity κ 4 t := by
  have hangle : enorm φ<2*π := lt_of_le_of_lt (hφ.trans hθ1) (by linarith [pi_gt_three])
  have hc := (left φ).toContinuousLinearMap.continuous
  have h := Gravity.monomial_prediction μ hμ x xv
    (fun t => q t+left φ (y t)) (fun t => qv t+left φ (yv t))
    (fun t => Gravity.field μ (q t)+u t+
      left φ (Gravity.gradient μ (q t) (y t)+cross φ (u t)))
    (fun t => force φ (u t)) ![2*μ/r^3*θ*L, 4*μ/(r-L)^4*L^2] ![2,4]
    hκ hk (by intro i; fin_cases i <;> dsimp <;> positivity) (show 0<r-2*L by linarith)
    (by simpa [Fin.sum_univ_two] using hclose) hlip (by
      intro t ht
      have hj := left_norm φ hangle (y t)
      have hb := (hybound t ht).trans (mul_le_of_le_one_right hL (pow_le_one₀ ht.1 ht.2))
      have hn := norm_sub_norm_le (q t+left φ (y t)) (left φ (y t))
      have hq' := hq t ht
      simp only [add_sub_cancel_right] at hn
      have hn' := norm_sub_norm_le (q t) (-left φ (y t))
      simp only [norm_neg, sub_neg_eq_add] at hn'
      linarith)
    hx hxv (hcq.add (hc.comp hy)) (hcqv.add (hc.comp hyv)) hdx hdxv
    (fun t ht => (hdq t ht).add (left_derivative φ (hdy t ht)))
    (fun t ht => (hdqv t ht).add (left_derivative φ (hdyv t ht))) hip hiv (by
      intro t ht
      have hb := GeometricSTMDefect.time_profile μ hμ φ (q t).ofLp (y t).ofLp (u t).ofLp
        (Gravity.field μ (q t)+u t).ofLp
        (Gravity.gradient μ (q t) (y t)+cross φ (u t)).ofLp
        hr (show L<r by linarith) hL ht.1 ht.2 le_rfl (hq t ht) (hybound t ht) hφ hθ1
        (by change enorm (Gravity.field3 μ (q t).ofLp+(u t).ofLp-_)≤0; simp [Gravity.field3, enorm])
        (by change enorm (Gravity.gradient3 μ (q t).ofLp (y t).ofLp+φ ⨯₃ (u t).ofLp-_)≤0
            simp [Gravity.gradient3, cross, enorm])
      simpa [GeometricSTMDefect.defect, left, force, Fin.sum_univ_two, Gravity.field3] using hb)
  simpa [Fin.sum_univ_two] using h

end GNC.OrbitalComparison.GeometricSTMPrediction
