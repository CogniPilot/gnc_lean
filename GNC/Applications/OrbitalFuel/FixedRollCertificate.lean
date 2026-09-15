import GNC.Applications.OrbitalFuel.SharedBiasCertificates
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix GNC.SharedBias GNC.FuelCertificate
open GNC.Applications.OrbitalFuel.SharedBiasExample (axis)
namespace GNC.Applications.OrbitalFuel.FixedRollCertificate
open SharedBiasCertificates.Earth

/-- Undo the 180-degree roll of the middle six-burn cycle. Both transverse
coordinates change sign; the nominal thrust coordinate is unchanged. -/
def fixedH (i : Fin 12) (j : Fin 18) (k : Fin 3) : ℝ :=
  if j.val / 6 % 2 = 1 ∧ k.val < 2 then -h i j k else h i j k
def witness : Fin 12 → GNC.Vec3 := ![![(-5451550000000/1250005948376481), (-149950000000/1250005948376481), (1249994051623519/1250005948376481)], ![(5451550000000/1250005948376481), (149950000000/1250005948376481), (1249994051623519/1250005948376481)], ![(43625600000000/10000047587022873), (536600000000/10000047587022873), (9999952412977127/10000047587022873)], ![(-43625600000000/10000047587022873), (-536600000000/10000047587022873), (9999952412977127/10000047587022873)], ![0, (1745160000000/400001903489641), (399998096510359/400001903489641)], ![0, (-1745160000000/400001903489641), (399998096510359/400001903489641)], ![(-8724680000000/2000009517460741), (-140160000000/2000009517460741), (1999990482539259/2000009517460741)], ![(8724680000000/2000009517460741), (140160000000/2000009517460741), (1999990482539259/2000009517460741)], ![(17415200000/4000019034873), (1126400000/4000019034873), (3999980965127/4000019034873)], ![(-17415200000/4000019034873), (-1126400000/4000019034873), (3999980965127/4000019034873)], ![0, (-1745160000000/400001903489641), (399998096510359/400001903489641)], ![0, (1745160000000/400001903489641), (399998096510359/400001903489641)]]
def multiplier : Fin 12 → ℝ := ![(32295595543/1000000000000), 0, 0, (10368496257/500000000000), (8019987717/1000000000000), 0, 0, (28317412023/1000000000000), 0, 0, 0, (81283879/6250000000)]
def cut : Fin 12 → Fin 18 → ℝ := fun i j => fixedH i j ⬝ᵥ witness i

theorem nominal_unchanged (i : Fin 12) (j : Fin 18) : fixedH i j 2 = h i j 2 := by
  simp [fixedH]

theorem witnesses : ∀ i, witness i ∈ GNC.ThrustSupport.Cap axis kappa := by
  intro i
  fin_cases i <;>
    norm_num [witness, axis, kappa, GNC.ThrustSupport.Cap, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two]

theorem multiplier_nonneg : ∀ i, 0 ≤ multiplier i := by
  intro i
  fin_cases i <;> norm_num [multiplier]

theorem lower_value : boxLower cut b c multiplier = (10577523790436038128930809080225845294967995841797026204186488986948930169123735459/74075484073616126846130169301442979854044049890107282064767800000000000000000000000) := by
  norm_num [boxLower, cut, fixedH, h, witness, b, c, multiplier, dotProduct, Fin.sum_univ_succ]

theorem fixed_common_lower (y : Fin 18 → ℝ)
    (hy : CommonFeasible axis kappa fixedH b y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    ((10577523790436038128930809080225845294967995841797026204186488986948930169123735459/74075484073616126846130169301442979854044049890107282064767800000000000000000000000) : ℝ) ≤ Cost c y := by
  rw [← lower_value]
  exact common_cost_lower axis kappa fixedH b c y witness multiplier witnesses hy hbox multiplier_nonneg

/-- Both sides retain a common bias. The change is the known roll schedule,
not an independent-uncertainty approximation on the comparator. -/
theorem roll_schedule_strict_saving (y : Fin 18 → ℝ)
    (hy : CommonFeasible axis kappa fixedH b y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) : Cost c x < Cost c y := by
  have hl := fixed_common_lower y hy hbox
  rw [cost_value]
  linarith

theorem roll_schedule_propellant_saving (y : Fin 18 → ℝ)
    (hy : CommonFeasible axis kappa fixedH b y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) (m exhaust : ℝ)
    (hm : 0 < m) (he : 0 < exhaust) :
    GNC.Propellant.consumedMass m exhaust (Cost c x) <
      GNC.Propellant.consumedMass m exhaust (Cost c y) :=
  GNC.Propellant.consumed_strictMono hm he (roll_schedule_strict_saving y hy hbox)
end GNC.Applications.OrbitalFuel.FixedRollCertificate
