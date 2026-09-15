import GNC.Applications.OrbitalFuel.BurnData.Block2

namespace GNC.Applications.OrbitalFuel.PolynomialBurn

def cells : Fin 18 → Fin 3 → Cell := ![cells0, cells1, cells2, cells3, cells4, cells5, cells6, cells7, cells8, cells9, cells10, cells11, cells12, cells13, cells14, cells15, cells16, cells17]

def centers : Fin 18 → Fin 10 → ℚ := ![center0, center1, center2, center3, center4, center5, center6, center7, center8, center9, center10, center11, center12, center13, center14, center15, center16, center17]

theorem cells_valid (j : Fin 18) (k : Fin 3) : (cells j k).Valid := by
  fin_cases j
  · exact cells0_valid k
  · exact cells1_valid k
  · exact cells2_valid k
  · exact cells3_valid k
  · exact cells4_valid k
  · exact cells5_valid k
  · exact cells6_valid k
  · exact cells7_valid k
  · exact cells8_valid k
  · exact cells9_valid k
  · exact cells10_valid k
  · exact cells11_valid k
  · exact cells12_valid k
  · exact cells13_valid k
  · exact cells14_valid k
  · exact cells15_valid k
  · exact cells16_valid k
  · exact cells17_valid k

theorem cells_join (j : Fin 18) (k : Fin 2) : (cells j k.castSucc).finish = (cells j k.succ).start := by
  fin_cases j
  · exact cells0_join k
  · exact cells1_join k
  · exact cells2_join k
  · exact cells3_join k
  · exact cells4_join k
  · exact cells5_join k
  · exact cells6_join k
  · exact cells7_join k
  · exact cells8_join k
  · exact cells9_join k
  · exact cells10_join k
  · exact cells11_join k
  · exact cells12_join k
  · exact cells13_join k
  · exact cells14_join k
  · exact cells15_join k
  · exact cells16_join k
  · exact cells17_join k

theorem cells_start (j : Fin 18) : (cells j 0).start = burnStart j := by
  fin_cases j
  · exact cells0_start
  · exact cells1_start
  · exact cells2_start
  · exact cells3_start
  · exact cells4_start
  · exact cells5_start
  · exact cells6_start
  · exact cells7_start
  · exact cells8_start
  · exact cells9_start
  · exact cells10_start
  · exact cells11_start
  · exact cells12_start
  · exact cells13_start
  · exact cells14_start
  · exact cells15_start
  · exact cells16_start
  · exact cells17_start

theorem cells_finish (j : Fin 18) : (cells j 2).finish = burnFinish j := by
  fin_cases j
  · exact cells0_finish
  · exact cells1_finish
  · exact cells2_finish
  · exact cells3_finish
  · exact cells4_finish
  · exact cells5_finish
  · exact cells6_finish
  · exact cells7_finish
  · exact cells8_finish
  · exact cells9_finish
  · exact cells10_finish
  · exact cells11_finish
  · exact cells12_finish
  · exact cells13_finish
  · exact cells14_finish
  · exact cells15_finish
  · exact cells16_finish
  · exact cells17_finish

theorem centers_error (j : Fin 18) (o : Fin 10) : |mean (cells j) o-centers j o| ≤ 1/10^25 := by
  fin_cases j
  · exact center0_error o
  · exact center1_error o
  · exact center2_error o
  · exact center3_error o
  · exact center4_error o
  · exact center5_error o
  · exact center6_error o
  · exact center7_error o
  · exact center8_error o
  · exact center9_error o
  · exact center10_error o
  · exact center11_error o
  · exact center12_error o
  · exact center13_error o
  · exact center14_error o
  · exact center15_error o
  · exact center16_error o
  · exact center17_error o

end GNC.Applications.OrbitalFuel.PolynomialBurn
