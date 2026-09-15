import GNC.Applications.OrbitalFuel.ChaserExtension

/-! Construct a whole-horizon nonlinear relative trajectory and prove that
the bounded extension agrees with the physical gravity field everywhere
on the mission. No existing trajectory or noncollision premise is used.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ChaserContinuation
open GNC GNC.Gravity Set ChaserExtension

def input (u : ℕ → ℝ → Vec3) (k : ℕ) (t : ℝ) : State :=
  (0,(1/4:ℝ) • u k t)

def rate (c a u : Vec3) (x : State) : State :=
  ((4:ℝ) • x.2,(1/4:ℝ) • (field3 1 (c+x.1)-field3 1 c-a+u))

theorem input_bound (u : ℕ → ℝ → Vec3) (k : ℕ) (t : ℝ)
    (hu : ‖u k t‖ ≤ (49/2500:ℝ)) : ‖input u k t‖ ≤ (49/10000:ℝ) := by
  simp only [input,Prod.norm_mk,norm_zero,norm_smul]
  norm_num
  linarith

theorem exists_relative (c a : ℝ → Vec3) (hc : Continuous c) (ha : Continuous a)
    (hr : ∀ t, (79/100:ℝ) ≤ GNC.enorm (c t))
    (hforce : ∀ t, ‖a t‖ ≤ (1/2500:ℝ))
    (u : ℕ → ℝ → Vec3) (nodes : ℕ → ℝ) (N : ℕ)
    (hu : ∀ k < N, Continuous (u k))
    (hub : ∀ k < N, ∀ t ∈ Ico (nodes k) (nodes (k+1)), ‖u k t‖ ≤ (49/2500:ℝ))
    (hn : Monotone nodes) (hzero : nodes 0 = 0) (hfinal : nodes N = (3/5:ℝ))
    (x₀ : State) (hi : ‖x₀‖ ≤ (1/10000:ℝ)) :
    ∃ x : ℝ → State, Continuous x ∧ x 0 = x₀ ∧
      (∀ t ∈ Icc (0:ℝ) (3/5), ‖x t‖ ≤ (22/625:ℝ)) ∧
      ∀ k < N, ∀ t ∈ Ioo (nodes k) (nodes (k+1)),
        HasDerivAt x (rate (c t) (a t) (u k t) (x t)) t := by
  have huc : ∀ k < N, Continuous (input u k) := by
    intro k hk
    exact continuous_const.prodMk ((hu k hk).const_smul (1/4:ℝ))
  obtain ⟨x,hx,hx₀,hd,hda⟩ := SwitchedODE.exists_solution
    (fun t => drift (c t) (a t)) 4 1
    (fun t => drift_lipschitz _ _ (hr t)) (drift_continuous c a hc ha hr)
    (fun t x => drift_bound _ _ (hr t) (hforce t) x)
    (input u) nodes N huc hn hzero x₀
  have hb : ∀ t ∈ Icc (0:ℝ) (3/5), ‖x t‖ ≤ (22/625:ℝ) := by
    intro t ht
    have h := SwitchedODE.norm_bound (fun t => drift (c t) (a t))
      (input u) nodes N 4 x (δ := (1/10000:ℝ))
      (D₀ := (1/10000:ℝ)) (D₁ := (49/10000:ℝ)) hn hzero hx hd
      (fun s _ => drift_lipschitz _ _ (hr s)) (by
        intro s hs
        rw [drift_zero]
        linarith [hforce s])
      (fun k hk s hs => input_bound u k s (hub k hk s hs))
      (by simpa only [hx₀] using hi) t (by simpa only [hfinal] using ht)
    norm_num only [NNReal.coe_ofNat,show (1/10000:ℝ)+49/10000 = 1/200 by norm_num] at h
    exact h.trans (SwitchedODE.coarse_solar_bound ht)
  refine ⟨x,hx,hx₀,hb,?_⟩
  intro k hk t ht
  have htT : t ∈ Icc (0:ℝ) (3/5) := by
    constructor
    · rw [← hzero]
      exact (hn (Nat.zero_le k)).trans ht.1.le
    · rw [← hfinal]
      exact ht.2.le.trans (hn (by omega))
  have he := drift_eq (c t) (a t) (x := x t) (by linarith [hb t htT])
  have h := hda k hk t ht
  rw [he] at h
  simpa only [input,rate,Prod.mk_add_mk,add_zero,smul_add] using h

end GNC.Applications.OrbitalFuel.ChaserContinuation
