import GNC.Magnus.FohCotangent
import Mathlib.Analysis.Calculus.LHopital

/-! Removable zero-angle limits of the cotangent coefficients.

A polynomial-times-sine/cosine numerator has a zero jet through degree six.
The seven displayed derivative identities and mathlib's L'Hopital theorem
prove its degree-seven quotient limit. Algebra then gives the actual limits
of c,d,alpha,beta,gamma. Explicit piecewise extensions install these values;
the raw quotient definitions are not asserted to have them at zero.
This proves limiting values, not the floating-point accuracy of a branch.
-/
noncomputable section
open Filter Set
open scoped Topology
namespace GNC.Magnus

/-- A finite vanishing derivative jet gives a punctured power-quotient limit.
This reuses mathlib's L'Hopital theorem, not a formal-series assumption. -/
theorem zero_jet_div_pow_limit (f : ℕ → ℝ → ℝ) (n : ℕ)
    (hd : ∀ k < n, ∀ x, HasDerivAt (f k) (f (k+1) x) x)
    (hz : ∀ k < n, f k 0 = 0) (hc : ContinuousAt (f n) 0) :
    Tendsto (fun x => f 0 x / x^n) (𝓝[≠] (0:ℝ))
      (𝓝 (f n 0 / (n.factorial : ℝ))) := by
  induction n generalizing f with
  | zero => simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  | succ n ih =>
    have hi := ih (fun k => f (k+1))
      (fun k hk x => hd (k+1) (by omega) x)
      (fun k hk => hz (k+1) (by omega)) hc
    have hlim : Tendsto (fun x => f 1 x / ((n+1:ℝ)*x^n)) (𝓝[≠] (0:ℝ))
        (𝓝 (f (n+1) 0 / ((n+1).factorial:ℝ))) := by
      simpa [Nat.factorial_succ, div_div, mul_comm] using hi.div_const (n+1:ℝ)
    apply HasDerivAt.lhopital_zero_nhdsNE
      (Eventually.of_forall (hd 0 (by omega)))
      (Eventually.of_forall (fun x => by simpa using (hasDerivAt_id x).pow (n+1)))
      ?_ ?_ ?_ hlim
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero (by positivity) (pow_ne_zero _ hx)
    · simpa [hz 0 (by omega)] using
        (hd 0 (by omega) 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · simpa using (continuousAt_id.pow (n+1)).tendsto.mono_left
        (show 𝓝[≠] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)

def fohCotNumeratorJet : ℕ → ℝ → ℝ
  | 0, x => ((1/1:ℝ)*x^0 + (-1/12:ℝ)*x^2 + (-1/720:ℝ)*x^4)*Real.sin (x/2) + ((-1/2:ℝ)*x^1)*Real.cos (x/2)
  | 1, x => ((1/12:ℝ)*x^1 + (-1/180:ℝ)*x^3)*Real.sin (x/2) + ((-1/24:ℝ)*x^2 + (-1/1440:ℝ)*x^4)*Real.cos (x/2)
  | 2, x => ((1/12:ℝ)*x^0 + (1/240:ℝ)*x^2 + (1/2880:ℝ)*x^4)*Real.sin (x/2) + ((-1/24:ℝ)*x^1 + (-1/180:ℝ)*x^3)*Real.cos (x/2)
  | 3, x => ((7/240:ℝ)*x^1 + (1/240:ℝ)*x^3)*Real.sin (x/2) + ((-7/480:ℝ)*x^2 + (1/5760:ℝ)*x^4)*Real.cos (x/2)
  | 4, x => ((7/240:ℝ)*x^0 + (19/960:ℝ)*x^2 + (-1/11520:ℝ)*x^4)*Real.sin (x/2) + ((-7/480:ℝ)*x^1 + (1/360:ℝ)*x^3)*Real.cos (x/2)
  | 5, x => ((3/64:ℝ)*x^1 + (-1/576:ℝ)*x^3)*Real.sin (x/2) + ((7/384:ℝ)*x^2 + (-1/23040:ℝ)*x^4)*Real.cos (x/2)
  | 6, x => ((3/64:ℝ)*x^0 + (-11/768:ℝ)*x^2 + (1/46080:ℝ)*x^4)*Real.sin (x/2) + ((23/384:ℝ)*x^1 + (-1/960:ℝ)*x^3)*Real.cos (x/2)
  | 7, x => ((-15/256:ℝ)*x^1 + (7/11520:ℝ)*x^3)*Real.sin (x/2) + ((1/12:ℝ)*x^0 + (-79/7680:ℝ)*x^2 + (1/92160:ℝ)*x^4)*Real.cos (x/2)
  | _, _ => 0

theorem fohCotNumeratorJet_deriv_0 (x : ℝ) :
    HasDerivAt (fohCotNumeratorJet 0) (fohCotNumeratorJet 1 x) x := by
  convert ((((((hasDerivAt_const x (1/1:ℝ)).mul ((hasDerivAt_id x).pow 0)).add ((hasDerivAt_const x (-1/12:ℝ)).mul ((hasDerivAt_id x).pow 2))).add ((hasDerivAt_const x (-1/720:ℝ)).mul ((hasDerivAt_id x).pow 4))).mul ((hasDerivAt_id x).div_const 2).sin).add (((hasDerivAt_const x (-1/2:ℝ)).mul ((hasDerivAt_id x).pow 1)).mul ((hasDerivAt_id x).div_const 2).cos)) using 1 <;> simp [fohCotNumeratorJet] <;> ring

theorem fohCotNumeratorJet_deriv_1 (x : ℝ) :
    HasDerivAt (fohCotNumeratorJet 1) (fohCotNumeratorJet 2 x) x := by
  convert (((((hasDerivAt_const x (1/12:ℝ)).mul ((hasDerivAt_id x).pow 1)).add ((hasDerivAt_const x (-1/180:ℝ)).mul ((hasDerivAt_id x).pow 3))).mul ((hasDerivAt_id x).div_const 2).sin).add ((((hasDerivAt_const x (-1/24:ℝ)).mul ((hasDerivAt_id x).pow 2)).add ((hasDerivAt_const x (-1/1440:ℝ)).mul ((hasDerivAt_id x).pow 4))).mul ((hasDerivAt_id x).div_const 2).cos)) using 1 <;> simp [fohCotNumeratorJet] <;> ring

theorem fohCotNumeratorJet_deriv_2 (x : ℝ) :
    HasDerivAt (fohCotNumeratorJet 2) (fohCotNumeratorJet 3 x) x := by
  convert ((((((hasDerivAt_const x (1/12:ℝ)).mul ((hasDerivAt_id x).pow 0)).add ((hasDerivAt_const x (1/240:ℝ)).mul ((hasDerivAt_id x).pow 2))).add ((hasDerivAt_const x (1/2880:ℝ)).mul ((hasDerivAt_id x).pow 4))).mul ((hasDerivAt_id x).div_const 2).sin).add ((((hasDerivAt_const x (-1/24:ℝ)).mul ((hasDerivAt_id x).pow 1)).add ((hasDerivAt_const x (-1/180:ℝ)).mul ((hasDerivAt_id x).pow 3))).mul ((hasDerivAt_id x).div_const 2).cos)) using 1 <;> simp [fohCotNumeratorJet] <;> ring

theorem fohCotNumeratorJet_deriv_3 (x : ℝ) :
    HasDerivAt (fohCotNumeratorJet 3) (fohCotNumeratorJet 4 x) x := by
  convert (((((hasDerivAt_const x (7/240:ℝ)).mul ((hasDerivAt_id x).pow 1)).add ((hasDerivAt_const x (1/240:ℝ)).mul ((hasDerivAt_id x).pow 3))).mul ((hasDerivAt_id x).div_const 2).sin).add ((((hasDerivAt_const x (-7/480:ℝ)).mul ((hasDerivAt_id x).pow 2)).add ((hasDerivAt_const x (1/5760:ℝ)).mul ((hasDerivAt_id x).pow 4))).mul ((hasDerivAt_id x).div_const 2).cos)) using 1 <;> simp [fohCotNumeratorJet] <;> ring

theorem fohCotNumeratorJet_deriv_4 (x : ℝ) :
    HasDerivAt (fohCotNumeratorJet 4) (fohCotNumeratorJet 5 x) x := by
  convert ((((((hasDerivAt_const x (7/240:ℝ)).mul ((hasDerivAt_id x).pow 0)).add ((hasDerivAt_const x (19/960:ℝ)).mul ((hasDerivAt_id x).pow 2))).add ((hasDerivAt_const x (-1/11520:ℝ)).mul ((hasDerivAt_id x).pow 4))).mul ((hasDerivAt_id x).div_const 2).sin).add ((((hasDerivAt_const x (-7/480:ℝ)).mul ((hasDerivAt_id x).pow 1)).add ((hasDerivAt_const x (1/360:ℝ)).mul ((hasDerivAt_id x).pow 3))).mul ((hasDerivAt_id x).div_const 2).cos)) using 1 <;> simp [fohCotNumeratorJet] <;> ring

theorem fohCotNumeratorJet_deriv_5 (x : ℝ) :
    HasDerivAt (fohCotNumeratorJet 5) (fohCotNumeratorJet 6 x) x := by
  convert (((((hasDerivAt_const x (3/64:ℝ)).mul ((hasDerivAt_id x).pow 1)).add ((hasDerivAt_const x (-1/576:ℝ)).mul ((hasDerivAt_id x).pow 3))).mul ((hasDerivAt_id x).div_const 2).sin).add ((((hasDerivAt_const x (7/384:ℝ)).mul ((hasDerivAt_id x).pow 2)).add ((hasDerivAt_const x (-1/23040:ℝ)).mul ((hasDerivAt_id x).pow 4))).mul ((hasDerivAt_id x).div_const 2).cos)) using 1 <;> simp [fohCotNumeratorJet] <;> ring

theorem fohCotNumeratorJet_deriv_6 (x : ℝ) :
    HasDerivAt (fohCotNumeratorJet 6) (fohCotNumeratorJet 7 x) x := by
  convert ((((((hasDerivAt_const x (3/64:ℝ)).mul ((hasDerivAt_id x).pow 0)).add ((hasDerivAt_const x (-11/768:ℝ)).mul ((hasDerivAt_id x).pow 2))).add ((hasDerivAt_const x (1/46080:ℝ)).mul ((hasDerivAt_id x).pow 4))).mul ((hasDerivAt_id x).div_const 2).sin).add ((((hasDerivAt_const x (23/384:ℝ)).mul ((hasDerivAt_id x).pow 1)).add ((hasDerivAt_const x (-1/960:ℝ)).mul ((hasDerivAt_id x).pow 3))).mul ((hasDerivAt_id x).div_const 2).cos)) using 1 <;> simp [fohCotNumeratorJet] <;> ring

theorem fohCotNumeratorJet_limit :
    Tendsto (fun x => fohCotNumeratorJet 0 x / x^7)
      (𝓝[≠] (0:ℝ)) (𝓝 (1/60480:ℝ)) := by
  have h := zero_jet_div_pow_limit fohCotNumeratorJet 7
    (by intro k hk x; interval_cases k
        exact fohCotNumeratorJet_deriv_0 x
        exact fohCotNumeratorJet_deriv_1 x
        exact fohCotNumeratorJet_deriv_2 x
        exact fohCotNumeratorJet_deriv_3 x
        exact fohCotNumeratorJet_deriv_4 x
        exact fohCotNumeratorJet_deriv_5 x
        exact fohCotNumeratorJet_deriv_6 x
    ) (by intro k hk; interval_cases k <;> norm_num [fohCotNumeratorJet])
    (by change ContinuousAt (fun x => fohCotNumeratorJet 7 x) 0
        dsimp only [fohCotNumeratorJet]
        fun_prop)
  convert h using 1 <;> norm_num [fohCotNumeratorJet, Nat.factorial]

theorem foh_sin_half_div_limit :
    Tendsto (fun x : ℝ => Real.sin (x/2) / x) (𝓝[≠] 0) (𝓝 (1/2:ℝ)) := by
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (((hasDerivAt_id (0:ℝ)).div_const 2).sin).tendsto_slope_zero

theorem fohCotC_fourth_quotient_limit :
    Tendsto (fun x => (fohCotC x - 1/12 - x^2/720) / x^4)
      (𝓝[≠] (0:ℝ)) (𝓝 (1/30240:ℝ)) := by
  have h := fohCotNumeratorJet_limit.div foh_sin_half_div_limit (by norm_num : (1/2:ℝ) ≠ 0)
  norm_num only [div_div, one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    foh_sin_half_div_limit.eventually_ne (by norm_num : (1/2:ℝ) ≠ 0)] with x hx hs
  have hx' : x ≠ 0 := hx
  have hs' : Real.sin (x/2) ≠ 0 := fun hh => hs (by rw [hh, zero_div])
  dsimp [fohCotC, fohCotNumeratorJet]
  field_simp [hx', hs']
  <;> ring

theorem fohCotC_limit : Tendsto fohCotC (𝓝[≠] (0:ℝ)) (𝓝 (1/12:ℝ)) := by
  have ht : Tendsto (fun x : ℝ => x) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have h := ((fohCotC_fourth_quotient_limit.mul (ht.pow 4)).add_const (1/12:ℝ)).add
    ((ht.pow 2).div_const 720)
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  field_simp [hx']
  <;> ring

theorem fohCotD_second_limit :
    Tendsto (fun x => (fohCotD x - 1/720) / x^2)
      (𝓝[≠] (0:ℝ)) (𝓝 (1/30240:ℝ)) := by
  apply fohCotC_fourth_quotient_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  dsimp only [fohCotD]
  field_simp [hx']
  <;> ring

theorem fohCotD_limit : Tendsto fohCotD (𝓝[≠] (0:ℝ)) (𝓝 (1/720:ℝ)) := by
  have ht : Tendsto (fun x : ℝ => x) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have h := (fohCotD_second_limit.mul (ht.pow 2)).add_const (1/720:ℝ)
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  field_simp [hx']
  <;> ring

theorem fohCotAlpha_limit : Tendsto fohCotAlpha (𝓝[≠] (0:ℝ)) (𝓝 (-1/240:ℝ)) := by
  convert ((fohCotC_limit.pow 2).neg.div_const 2).sub (fohCotD_limit.div_const 2) using 1 <;> norm_num

theorem fohCotBeta_limit : Tendsto fohCotBeta (𝓝[≠] (0:ℝ)) (𝓝 (1/240:ℝ)) := by
  convert fohCotD_limit.const_mul 3 using 1 <;> norm_num

theorem fohCotGamma_limit : Tendsto fohCotGamma (𝓝[≠] (0:ℝ)) (𝓝 (1/30240:ℝ)) := by
  have h := ((fohCotD_limit.mul (fohCotC_limit.add_const (1/12:ℝ))).sub
    (fohCotD_second_limit.const_mul 5)).div_const 2
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  dsimp only [fohCotGamma, fohCotD]
  field_simp [hx']
  <;> ring

/-- A removable value is explicitly installed; the raw quotient is not
silently treated as if it had that value at zero. -/
def fohCotExtend (f : ℝ → ℝ) (value x : ℝ) : ℝ := if x=0 then value else f x

theorem fohCotExtend_continuousAt_zero (f : ℝ → ℝ) (value : ℝ)
    (h : Tendsto f (𝓝[≠] (0:ℝ)) (𝓝 value)) :
    ContinuousAt (fohCotExtend f value) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  rw [show fohCotExtend f value 0 = value by simp [fohCotExtend]]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  simp [fohCotExtend, hx']

theorem fohCot_removable_extensions :
    ContinuousAt (fohCotExtend fohCotC (1/12)) 0 ∧
    ContinuousAt (fohCotExtend fohCotD (1/720)) 0 ∧
    ContinuousAt (fohCotExtend fohCotAlpha (-1/240)) 0 ∧
    ContinuousAt (fohCotExtend fohCotBeta (1/240)) 0 ∧
    ContinuousAt (fohCotExtend fohCotGamma (1/30240)) 0 :=
  ⟨fohCotExtend_continuousAt_zero _ _ fohCotC_limit,
   fohCotExtend_continuousAt_zero _ _ fohCotD_limit,
   fohCotExtend_continuousAt_zero _ _ fohCotAlpha_limit,
   fohCotExtend_continuousAt_zero _ _ fohCotBeta_limit,
   fohCotExtend_continuousAt_zero _ _ fohCotGamma_limit⟩

end GNC.Magnus
