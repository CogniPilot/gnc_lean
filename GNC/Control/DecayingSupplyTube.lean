import GNC.Control.Lyapunov

/-! Preserve a proved inner-loop transient instead of replacing its energy
by a constant worst-case bound. This scalar comparison is independent of
coordinates; its orbital use is the exact log/rate-to-thrust cascade.
The two distinct decay rates need not have a time-scale separation.
-/
noncomputable section
open Real Set
namespace GNC.DecayingSupplyTube

def envelope (v₀ lam c S H t : ℝ) : ℝ :=
  v₀*exp (-lam*t)+(S/lam)*(1-exp (-lam*t))+
    (H/(lam-c))*(exp (-c*t)-exp (-lam*t))

theorem initial (v₀ lam c S H : ℝ) : envelope v₀ lam c S H 0 = v₀ := by
  simp [envelope]

theorem derivative (v₀ lam c S H t : ℝ) (hlam : lam ≠ 0) (hne : lam-c ≠ 0) :
    HasDerivAt (envelope v₀ lam c S H)
      (-lam*envelope v₀ lam c S H t+S+H*exp (-c*t)) t := by
  have hl : HasDerivAt (fun s : ℝ => exp (-lam*s)) (-lam*exp (-lam*t)) t := by
    simpa [mul_comm] using (((hasDerivAt_id t).const_mul (-lam)).exp)
  have hc : HasDerivAt (fun s : ℝ => exp (-c*s)) (-c*exp (-c*t)) t := by
    simpa [mul_comm] using (((hasDerivAt_id t).const_mul (-c)).exp)
  convert ((hl.const_mul v₀).add (((hasDerivAt_const t (1:ℝ)).sub hl).const_mul
    (S/lam))).add ((hc.sub hl).const_mul (H/(lam-c))) using 1
  dsimp [envelope]
  field_simp [hlam,hne]
  ring

/-- An exact two-exponential barrier for an exponentially decaying supply.
This theorem does not assume that the supplied energy is nonnegative or
that one decay is faster; callers establish physical energy properties. -/
theorem bound {V dV : ℝ → ℝ} {v₀ lam c S H T : ℝ}
    (hlam : lam ≠ 0) (hne : lam-c ≠ 0) (hinit : V 0 ≤ v₀)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (dV t) t)
    (hs : ∀ t ∈ Ico 0 T, dV t ≤ -lam*V t+S+H*exp (-c*t)) :
    ∀ t ∈ Icc 0 T, V t ≤ envelope v₀ lam c S H t := by
  have h := Lyapunov.exponential_bound_on
    (V := fun t => V t-envelope v₀ lam c S H t) (c := lam)
    (fun t ht => (hV t ht).sub (derivative v₀ lam c S H t hlam hne)) (by
      intro t ht
      have h := hs t ht
      linarith)
  intro t ht
  have hb := h t ht
  dsimp only at hb
  rw [initial] at hb
  have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hinit)
    (exp_pos (-lam*(t-0))).le
  linarith

/-- Exact weighted Young inequality used to retain the pointing transient.
The weight is a freely chosen positive design parameter, not a tolerance. -/
theorem weighted_force_square (a b η : ℝ) (hη : 0 < η) :
    (a+b)^2 ≤ (1+η)*a^2+(1+1/η)*b^2 := by
  have h := div_nonneg (sq_nonneg (η*a-b)) hη.le
  have he : (η*a-b)^2/η =
      (1+η)*a^2+(1+1/η)*b^2-(a+b)^2 := by
    field_simp
    ring
  rw [he] at h
  linarith

end GNC.DecayingSupplyTube
