import GNC.Lie.ExponentialCoordinates

/-! Derivatives of the coordinate formulas and the Maurer–Cartan identity
needed to identify the SE₂(3) Jacobian blocks. -/
noncomputable section
open Matrix Real
open scoped Matrix Topology
namespace GNC.Jacobian

def leftDerivative (q u v : Vec3) : Vec3 :=
  (((enorm q)*sin (enorm q)-2+2*cos (enorm q))*(q ⬝ᵥ u)/enorm q^4) • (q ⨯₃ v) +
  ((1-cos (enorm q))/enorm q^2) • (u ⨯₃ v) +
  ((3*sin (enorm q)-2*enorm q-enorm q*cos (enorm q))*(q ⬝ᵥ u)/enorm q^5) •
    (q ⨯₃ (q ⨯₃ v)) +
  ((enorm q-sin (enorm q))/enorm q^3) •
    (u ⨯₃ (q ⨯₃ v) + q ⨯₃ (u ⨯₃ v))

theorem leftAt_curve_derivative (q u : Vec3) {V : ℝ → Vec3} {v' : Vec3}
    (hV : HasDerivAt V v' 0) (hq : 0 < enorm q) :
    HasDerivAt (fun s => leftAt (q+s • u) (V s))
      (leftDerivative q u (V 0) + leftAt q v') 0 := by
  have hq0 : q ≠ 0 := mt (enorm_eq_zero_iff q).mpr hq.ne'
  have hp : HasDerivAt (fun s : ℝ => q+s • u) u 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add q
  have hn : HasDerivAt (fun s : ℝ => enorm (q+s • u)) (q ⬝ᵥ u/enorm q) 0 := by
    simpa using affine_enorm_derivative q u 0 (by simpa using hq0)
  have ha := (hn.cos.const_sub 1).div (hn.pow 2) (by simpa using pow_ne_zero 2 hq.ne')
  have hb := (hn.sub hn.sin).div (hn.pow 3) (by simpa using pow_ne_zero 3 hq.ne')
  have hx := cross_derivative hp hV
  have hxx := cross_derivative hp hx
  convert (hV.add (ha.smul hx)).add (hb.smul hxx) using 1
  dsimp [leftDerivative, leftAt]
  simp only [zero_smul, add_zero, map_add]
  match_scalars <;> field_simp <;> ring

theorem Q_formula (q u v : Vec3) (hq : 0 < enorm q) : Q q u v = leftDerivative q u v := by
  have h := leftAt_curve_derivative q u (hasDerivAt_const (0:ℝ) v) hq
  simpa [Q] using h.deriv

theorem Q_axis (k u v : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) :
    Q (t • k) u v =
      ((t*sin t-2+2*cos t)/t^2*(k ⬝ᵥ u)) • (k ⨯₃ v) +
      ((1-cos t)/t^2) • (u ⨯₃ v) +
      ((3*sin t-2*t-t*cos t)/t^2*(k ⬝ᵥ u)) • (k ⨯₃ (k ⨯₃ v)) +
      ((t-sin t)/t^2) • (u ⨯₃ (k ⨯₃ v) + k ⨯₃ (u ⨯₃ v)) := by
  have hn : enorm (t • k) = t := by
    rw [enorm_smul, Gravity.unit_enorm k hk, abs_of_pos ht, mul_one]
  rw [Q_formula _ _ _ (by simpa [hn]), leftDerivative, hn]
  simp only [map_smul, LinearMap.smul_apply, smul_dotProduct, smul_eq_mul, smul_smul,
    smul_add]
  match_scalars <;> field_simp <;> ring

theorem cross_curl₁ (k u v : Vec3) :
    (k ⬝ᵥ u) • (k ⨯₃ v) - (k ⬝ᵥ v) • (k ⨯₃ u) = -(k ⨯₃ (k ⨯₃ (u ⨯₃ v))) := by
  ext i; fin_cases i <;>
    simp [cross_apply, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem cross_curl₂ (k u v : Vec3) (hk : k ⬝ᵥ k = 1) :
    (k ⬝ᵥ u) • (k ⨯₃ (k ⨯₃ v)) - (k ⬝ᵥ v) • (k ⨯₃ (k ⨯₃ u)) =
      k ⨯₃ (u ⨯₃ v) := by
  simp only [cross_cross_eq_smul_sub_smul', hk, one_smul]
  rw [dotProduct_comm u k]
  module

theorem cross_curl₃ (k u v : Vec3) :
    u ⨯₃ (k ⨯₃ v) - v ⨯₃ (k ⨯₃ u) = k ⨯₃ (u ⨯₃ v) := by
  simp only [cross_cross_eq_smul_sub_smul']
  rw [dotProduct_comm u v, dotProduct_comm u k]
  module

theorem Q_antisymmetric_axis (k u v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) :
    Q (t • k) u v - Q (t • k) v u =
      (2*(1-cos t)/t^2) • (u ⨯₃ v) -
      ((t*sin t-2+2*cos t)/t^2) • (k ⨯₃ (k ⨯₃ (u ⨯₃ v))) +
      ((1-cos t)/t) • (k ⨯₃ (u ⨯₃ v)) := by
  rw [Q_axis k u v hk t ht, Q_axis k v u hk t ht]
  have h1 := cross_curl₁ k u v
  have h2 := cross_curl₂ k u v hk
  have h3 := cross_curl₃ k u v
  rw [← cross_anticomm u v]
  simp only [map_neg]
  linear_combination (norm := skip) ((t*sin t-2+2*cos t)/t^2) • h1 +
    ((3*sin t-2*t-t*cos t)/t^2) • h2 + ((t-sin t)/t^2) • h3
  all_goals match_scalars <;> field_simp <;> ring

theorem cross_cross_axis (k u v : Vec3) :
    (k ⨯₃ u) ⨯₃ (k ⨯₃ v) = Axis.axial k (u ⨯₃ v) := by
  ext i; fin_cases i <;>
    simp [Axis.axial, cross_apply, dotProduct, Fin.sum_univ_succ] <;> ring

theorem planeMap_cross_pair (k u v : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) :
    planeMap k a b u ⨯₃ planeMap k a b v =
      (a^2+b^2) • Axis.axial k (u ⨯₃ v) +
        a • Axis.transverse k (u ⨯₃ v) + b • (k ⨯₃ (u ⨯₃ v)) := by
  have he : planeMap k a b u ⨯₃ planeMap k a b v =
      a^2 • (u ⨯₃ v) + (a*(1-a)) •
        ((k ⬝ᵥ u) • (k ⨯₃ v) - (k ⬝ᵥ v) • (k ⨯₃ u)) +
      (a*b) • (u ⨯₃ (k ⨯₃ v) - v ⨯₃ (k ⨯₃ u)) + ((1-a)*b) •
        ((k ⬝ᵥ u) • (k ⨯₃ (k ⨯₃ v)) - (k ⬝ᵥ v) • (k ⨯₃ (k ⨯₃ u))) +
      b^2 • ((k ⨯₃ u) ⨯₃ (k ⨯₃ v)) := by
    simp only [planeMap, Axis.axial, Axis.transverse, map_add, map_sub, map_smul,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_smul,
      cross_self, smul_zero, zero_add, add_zero]
    rw [← cross_anticomm k u, ← cross_anticomm (k ⨯₃ u) v,
      ← cross_anticomm k (k ⨯₃ u)]
    module
  rw [he, cross_curl₁, cross_curl₂ k u v hk, cross_curl₃,
    cross_cross_axis, Axis.cross_sq k (u ⨯₃ v) hk]
  unfold Axis.transverse
  module

/-- Maurer–Cartan identity for the actual SO(3) Jacobian. -/
theorem Q_antisymmetric (k u v : Vec3) (hk : k ⬝ᵥ k = 1)
    (t : ℝ) (ht : 0 < t) :
    Q (t • k) u v - Q (t • k) v u = left k t u ⨯₃ left k t v := by
  rw [Q_antisymmetric_axis k u v hk t ht]
  change _ = planeMap k (sin t/t) ((1-cos t)/t) u ⨯₃ planeMap k (sin t/t) ((1-cos t)/t) v
  rw [planeMap_cross_pair k u v hk]
  rw [Axis.cross_sq k (u ⨯₃ v) hk]
  have hc : (sin t/t)^2+((1-cos t)/t)^2 = 2*(1-cos t)/t^2 := by
    field_simp
    nlinarith [sin_sq_add_cos_sq t]
  rw [hc]
  unfold Axis.transverse
  match_scalars <;> field_simp <;> ring

end GNC.Jacobian
