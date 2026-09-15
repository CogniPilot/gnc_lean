import GNC.Applications.OrbitalFuel.TerminalGravityData.Block3

namespace GNC.Applications.OrbitalFuel.TerminalGravity

def nu : Fin 32 → Fin 6 → ℚ := ![nu0, nu1, nu2, nu3, nu4, nu5, nu6, nu7, nu8, nu9, nu10, nu11, nu12, nu13, nu14, nu15, nu16, nu17, nu18, nu19, nu20, nu21, nu22, nu23, nu24, nu25, nu26, nu27, nu28, nu29, nu30, nu31]
def budget : Fin 32 → Fin 6 → ℚ := ![budget0, budget1, budget2, budget3, budget4, budget5, budget6, budget7, budget8, budget9, budget10, budget11, budget12, budget13, budget14, budget15, budget16, budget17, budget18, budget19, budget20, budget21, budget22, budget23, budget24, budget25, budget26, budget27, budget28, budget29, budget30, budget31]

theorem cell_certificate (j : Fin 32) (i : Fin 6) :
    0 < nu j i ∧ youngIntegral j i (nu j i) ≤ budget j i := by
  fin_cases j
  · exact cell0_certificate i
  · exact cell1_certificate i
  · exact cell2_certificate i
  · exact cell3_certificate i
  · exact cell4_certificate i
  · exact cell5_certificate i
  · exact cell6_certificate i
  · exact cell7_certificate i
  · exact cell8_certificate i
  · exact cell9_certificate i
  · exact cell10_certificate i
  · exact cell11_certificate i
  · exact cell12_certificate i
  · exact cell13_certificate i
  · exact cell14_certificate i
  · exact cell15_certificate i
  · exact cell16_certificate i
  · exact cell17_certificate i
  · exact cell18_certificate i
  · exact cell19_certificate i
  · exact cell20_certificate i
  · exact cell21_certificate i
  · exact cell22_certificate i
  · exact cell23_certificate i
  · exact cell24_certificate i
  · exact cell25_certificate i
  · exact cell26_certificate i
  · exact cell27_certificate i
  · exact cell28_certificate i
  · exact cell29_certificate i
  · exact cell30_certificate i
  · exact cell31_certificate i

def gain : Fin 6 → ℚ := ![197/1000,175/1000,171/1000,721/1000,556/1000,54/100]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gain_budget : ∀ i, (∑ j : Fin 32, budget j i) ≤ gain i := by decide +kernel

end GNC.Applications.OrbitalFuel.TerminalGravity
