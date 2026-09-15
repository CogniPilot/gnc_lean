import GNC.Lie.ControlGeometry
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Analytic identification of the M remainder with the derivative of the
inverse SO(3) Jacobian. This is the differentiation step in Lemma 4. -/
noncomputable section
open Matrix Real
open scoped Matrix Topology
namespace GNC.Jacobian

theorem cross_derivative {f g : ℝ → Vec3} {u v : Vec3} {t : ℝ}
    (hf : HasDerivAt f u t) (hg : HasDerivAt g v t) :
    HasDerivAt (fun s => f s ⨯₃ g s) (u ⨯₃ g t + f t ⨯₃ v) t := by
  have hf' := hasDerivAt_pi.mp hf
  have hg' := hasDerivAt_pi.mp hg
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert ((hf' 1).mul (hg' 2)).sub ((hf' 2).mul (hg' 1)) using 1 <;>
      simp [cross_apply] <;> ring
  · convert ((hf' 2).mul (hg' 0)).sub ((hf' 0).mul (hg' 2)) using 1 <;>
      simp [cross_apply] <;> ring
  · convert ((hf' 0).mul (hg' 1)).sub ((hf' 1).mul (hg' 0)) using 1 <;>
      simp [cross_apply] <;> ring

theorem affine_enorm_derivative (q u : Vec3) (s : ℝ) (hq : q+s • u ≠ 0) :
    HasDerivAt (fun z => enorm (q+z • u)) ((q+s • u) ⬝ᵥ u / enorm (q+s • u)) s := by
  have hp : HasDerivAt (fun z : ℝ => (WithLp.toLp 2 q : E3)+z • WithLp.toLp 2 u)
      (WithLp.toLp 2 u) s := by
    simpa using ((hasDerivAt_id s).smul_const (WithLp.toLp 2 u : E3)).const_add (WithLp.toLp 2 q)
  have hn : (WithLp.toLp 2 q : E3)+s • WithLp.toLp 2 u ≠ 0 := by
    intro h; exact hq (congrArg WithLp.ofLp h)
  have he := Gravity.norm_derivative hp hn
  change HasDerivAt (fun z => enorm (q+z • u))
    (inner ℝ (WithLp.toLp 2 (q+s • u) : E3) (WithLp.toLp 2 u) / enorm (q+s • u)) s at he
  rw [Gravity.inner_toLp] at he
  exact he

/-- Inverse Jacobian as a function of the rotation vector itself. -/
def inverseAt (q v : Vec3) : Vec3 :=
  v - (1/2 : ℝ) • (q ⨯₃ v) +
    (Coefficients.beta (enorm q)/enorm q^2) • (q ⨯₃ (q ⨯₃ v))

def inverseDerivative (q u v : Vec3) : Vec3 :=
  -(1/2 : ℝ) • (u ⨯₃ v) +
    ((Coefficients.alpha (enorm q)*enorm q - 2*Coefficients.beta (enorm q)) *
      (q ⬝ᵥ u)/enorm q^4) • (q ⨯₃ (q ⨯₃ v)) +
    (Coefficients.beta (enorm q)/enorm q^2) •
      (u ⨯₃ (q ⨯₃ v) + q ⨯₃ (u ⨯₃ v))

/-- Actual directional derivative, allowing the argument v to move as well. -/
theorem inverseAt_curve_derivative (q u : Vec3) {V : ℝ → Vec3} {v' : Vec3}
    (hV : HasDerivAt V v' 0) (hq : 0 < enorm q) (hqπ : enorm q < π) :
    HasDerivAt (fun s => inverseAt (q+s • u) (V s))
      (inverseDerivative q u (V 0) + inverseAt q v') 0 := by
  have hq0 : q ≠ 0 := mt (enorm_eq_zero_iff q).mpr hq.ne'
  have hp : HasDerivAt (fun s : ℝ => q+s • u) u 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add q
  have hn : HasDerivAt (fun s : ℝ => enorm (q+s • u)) (q ⬝ᵥ u/enorm q) 0 := by
    simpa using affine_enorm_derivative q u 0 (by simpa using hq0)
  have hb0 : HasDerivAt Coefficients.beta (Coefficients.alpha (enorm q))
      (enorm (q+(0:ℝ) • u)) := by simpa using Coefficients.beta_derivative (enorm q) hq hqπ
  have hb := hb0.comp 0 hn
  have hc := hb.div (hn.pow 2) (by simpa using pow_ne_zero 2 hq.ne')
  have hx := cross_derivative hp hV
  have hxx := cross_derivative hp hx
  convert (hV.sub (hx.const_smul (1/2:ℝ))).add (hc.smul hxx) using 1
  dsimp [inverseDerivative, inverseAt]
  simp only [zero_smul, add_zero, map_add]
  match_scalars <;> field_simp <;> ring

theorem inverseAt_derivative (q u v : Vec3) (hq : 0 < enorm q) (hqπ : enorm q < π) :
    HasDerivAt (fun s : ℝ => inverseAt (q+s • u) v) (inverseDerivative q u v) 0 := by
  simpa [inverseAt] using inverseAt_curve_derivative q u (hasDerivAt_const 0 v) hq hqπ

/-- Inverse-Jacobian differentiation along an arbitrary differentiable path. -/
theorem inverseAt_path_derivative {q v : ℝ → Vec3} {dq dv : Vec3} {t : ℝ}
    (hq : HasDerivAt q dq t) (hv : HasDerivAt v dv t)
    (hpos : 0 < enorm (q t)) (hπ : enorm (q t) < π) :
    HasDerivAt (fun s => inverseAt (q s) (v s))
      (inverseDerivative (q t) dq (v t)+inverseAt (q t) dv) t := by
  have hp : HasDerivAt (fun s => (WithLp.toLp 2 (q s) : E3)) (WithLp.toLp 2 dq) t :=
    (WithLp.linearEquiv 2 ℝ Vec3).symm.toLinearMap.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hq
  have hn := Gravity.norm_derivative hp (by
    intro h; have hz : q t = 0 := congrArg WithLp.ofLp h
    simpa [hz, enorm] using hpos)
  change HasDerivAt (fun s => enorm (q s))
    (inner ℝ (WithLp.toLp 2 (q t) : E3) (WithLp.toLp 2 dq)/enorm (q t)) t at hn
  rw [Gravity.inner_toLp] at hn
  have hb := (Coefficients.beta_derivative (enorm (q t)) hpos hπ).comp t hn
  have hc := hb.div (hn.pow 2) (pow_ne_zero 2 hpos.ne')
  have hx := cross_derivative hq hv
  have hxx := cross_derivative hq hx
  convert (hv.sub (hx.const_smul (1/2:ℝ))).add (hc.smul hxx) using 1
  dsimp [inverseDerivative, inverseAt]
  simp only [map_add]
  match_scalars <;> field_simp <;> ring

theorem inverseAt_axis (k v : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) :
    inverseAt (t • k) v = leftInv k t v := by
  have hn : enorm (t • k) = t := by
    rw [enorm_smul, Gravity.unit_enorm k hk, abs_of_pos ht, mul_one]
  rw [inverseAt, hn, leftInv_closed k v hk t ht.ne']

/-- M from Lemma 4 is the derivative of B plus the first-order cross term. -/
theorem derivative_remainder (k u v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) :
    inverseDerivative (t • k) u v + (1/2 : ℝ) • (u ⨯₃ v) =
      Control.mAction k (Coefficients.alpha t) (Coefficients.beta t/t) u v := by
  have hn : enorm (t • k) = t := by
    rw [enorm_smul, Gravity.unit_enorm k hk, abs_of_pos ht, mul_one]
  simp only [inverseDerivative, hn, map_smul, LinearMap.smul_apply,
    smul_smul, smul_dotProduct, smul_eq_mul, cross_cross_eq_smul_sub_smul']
  ext i
  simp [Control.mAction, Axis.transverse, Axis.axial, hk, dotProduct_comm u k]
  field_simp; ring

/-- Lemma 4 bound for the actual inverse-Jacobian derivative. -/
theorem inverseDerivative_remainder_bound (k u v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    enorm (inverseDerivative (t • k) u v + (1/2 : ℝ) • (u ⨯₃ v)) ≤
      Coefficients.alpha t*enorm u*enorm v := by
  rw [derivative_remainder k u v hk t ht]
  exact Control.mAction_alpha_bound k u v hk t ht htπ

def leftAt (q v : Vec3) : Vec3 :=
  v + ((1-cos (enorm q))/enorm q^2) • (q ⨯₃ v) +
    ((enorm q-sin (enorm q))/enorm q^3) • (q ⨯₃ (q ⨯₃ v))

def unitAxis (q : Vec3) : Vec3 := (enorm q)⁻¹ • q

theorem unitAxis_unit (q : Vec3) (hq : 0 < enorm q) : unitAxis q ⬝ᵥ unitAxis q = 1 := by
  simp only [unitAxis, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dot_self_lengthSq, ← enorm_sq]
  field_simp

theorem unitAxis_reconstruct (q : Vec3) (hq : 0 < enorm q) : enorm q • unitAxis q = q := by
  simp [unitAxis, smul_smul, hq.ne']

theorem leftAt_axis (k v : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) :
    leftAt (t • k) v = left k t v := by
  have hn : enorm (t • k) = t := by
    rw [enorm_smul, Gravity.unit_enorm k hk, abs_of_pos ht, mul_one]
  rw [leftAt, hn, left_closed k v hk t ht.ne']

theorem leftAt_eq (q v : Vec3) (hq : 0 < enorm q) :
    leftAt q v = left (unitAxis q) (enorm q) v := by
  simpa only [unitAxis_reconstruct q hq] using
    leftAt_axis (unitAxis q) v (unitAxis_unit q hq) (enorm q) hq

theorem inverseAt_eq (q v : Vec3) (hq : 0 < enorm q) :
    inverseAt q v = leftInv (unitAxis q) (enorm q) v := by
  simpa only [unitAxis_reconstruct q hq] using
    inverseAt_axis (unitAxis q) v (unitAxis_unit q hq) (enorm q) hq

theorem inverseAt_leftAt (q v : Vec3) (hq : 0 < enorm q) (hqπ : enorm q < 2*π) :
    inverseAt q (leftAt q v) = v := by
  rw [leftAt_eq q v hq, inverseAt_eq q _ hq]
  exact leftInv_left (unitAxis q) v (unitAxis_unit q hq) (enorm q) hq hqπ

theorem leftAt_inverseAt (q v : Vec3) (hq : 0 < enorm q) (hqπ : enorm q < 2*π) :
    leftAt q (inverseAt q v) = v := by
  rw [inverseAt_eq q v hq, leftAt_eq q _ hq]
  exact left_leftInv (unitAxis q) v (unitAxis_unit q hq) (enorm q) hq hqπ

/-- Q(u,q) is the directional derivative of the SO(3) left Jacobian at q,
as used in equation (51). No derivative existence is assumed. -/
def Q (q u v : Vec3) : Vec3 := deriv (fun s : ℝ => leftAt (q+s • u) v) 0

theorem leftAt_curve_differentiable (q u v : Vec3) (hq : 0 < enorm q) :
    DifferentiableAt ℝ (fun s : ℝ => leftAt (q+s • u) v) 0 := by
  have hq0 : q ≠ 0 := mt (enorm_eq_zero_iff q).mpr hq.ne'
  have hp : HasDerivAt (fun s : ℝ => q+s • u) u 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add q
  have hn := (affine_enorm_derivative q u 0 (by simpa using hq0)).differentiableAt
  have hx := (cross_derivative hp (hasDerivAt_const 0 v))
  have hxx := cross_derivative hp hx
  have h1 := (hn.cos.const_sub 1).div (hn.pow 2) (by simpa using pow_ne_zero 2 hq.ne')
  have h2 := (hn.sub hn.sin).div (hn.pow 3) (by simpa using pow_ne_zero 3 hq.ne')
  exact ((differentiableAt_const v).add (h1.smul hx.differentiableAt)).add
    (h2.smul hxx.differentiableAt)

/-- Analytic inverse differentiation: DB[u] = -B Q(u) B. -/
theorem inverseDerivative_Q (q u v : Vec3) (hq : 0 < enorm q) (hqπ : enorm q < π) :
    inverseDerivative q u v = -inverseAt q (Q q u (inverseAt q v)) := by
  have identity_derivative (w : Vec3) :
      inverseDerivative q u (leftAt q w) + inverseAt q (Q q u w) = 0 := by
    have hJ : HasDerivAt (fun s : ℝ => leftAt (q+s • u) w) (Q q u w) 0 :=
      (leftAt_curve_differentiable q u w hq).hasDerivAt
    have hd := inverseAt_curve_derivative q u hJ hq hqπ
    have hq0 : q ≠ 0 := mt (enorm_eq_zero_iff q).mpr hq.ne'
    have hn := (affine_enorm_derivative q u 0 (by simpa using hq0)).continuousAt
    have hmem : ∀ᶠ s : ℝ in 𝓝 0, enorm (q+s • u) ∈ Set.Ioo 0 π :=
      hn (by simpa using Ioo_mem_nhds hq hqπ)
    have he : (fun s : ℝ => w) =ᶠ[𝓝 0]
        (fun s => inverseAt (q+s • u) (leftAt (q+s • u) w)) := by
      filter_upwards [hmem] with s hs
      exact (inverseAt_leftAt (q+s • u) w hs.1 (by linarith [hs.2, Real.pi_pos])).symm
    have hh := (hd.congr_of_eventuallyEq he).unique (hasDerivAt_const 0 w)
    simpa using hh
  have h := identity_derivative (inverseAt q v)
  rw [leftAt_inverseAt q v hq (by linarith [Real.pi_pos])] at h
  exact eq_neg_of_add_eq_zero_left h

def M (q u v : Vec3) : Vec3 := -inverseAt q (Q q u (inverseAt q v)) + (1/2:ℝ) • (u ⨯₃ v)

/-- Lemma 4, now for the Q block obtained by differentiating the actual J. -/
theorem M_bound (k u v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    enorm (M (t • k) u v) ≤ Coefficients.alpha t*enorm u*enorm v := by
  have hn : enorm (t • k) = t := by
    rw [enorm_smul, Gravity.unit_enorm k hk, abs_of_pos ht, mul_one]
  rw [M, ← inverseDerivative_Q (t • k) u v (by simpa [hn]) (by simpa [hn])]
  exact inverseDerivative_remainder_bound k u v hk t ht htπ

theorem M_eq_geometric (k u v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    M (t • k) u v = Control.mAction k (Coefficients.alpha t) (Coefficients.beta t/t) u v := by
  have hn : enorm (t • k) = t := by
    rw [enorm_smul, Gravity.unit_enorm k hk, abs_of_pos ht, mul_one]
  rw [M, ← inverseDerivative_Q (t • k) u v (by simpa [hn]) (by simpa [hn]),
    derivative_remainder k u v hk t ht]

/-- A formal counterexample to Remark 5's unconditional equality assertion,
using the actual Q derivative and inverse Jacobian. -/
theorem remark5_counterexample (k : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) (htπ : t < π) :
    enorm (M (t • k) k k) < Coefficients.alpha t*enorm k*enorm k := by
  rw [M_eq_geometric k k k hk t ht htπ]
  exact Control.remark5_strict k hk t ht htπ

end GNC.Jacobian
