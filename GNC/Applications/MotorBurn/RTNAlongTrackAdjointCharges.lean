import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step00AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step01AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step02AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step03AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step04AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step05AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step06AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step07AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step08AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step09AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step10AdjointSupport1
import GNC.Applications.MotorBurn.Data.RTNCircle2Time6Step11AdjointSupport1
import GNC.Applications.MotorBurn.RTNAlongTrackAdjoint

/-! All initial, interface, terminal and support charges, independently
checked against stored coefficient records. Physical composition is separate. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace GNC.MotorBurn.RTNAlongTrackAdjoint
open ParametricBox
def transverseLimit : ℕ → ℚ
  | 0 => Data.RTNCircle2Time6Step00AdjointSupport1.transverseLimit
  | 1 => Data.RTNCircle2Time6Step01AdjointSupport1.transverseLimit
  | 2 => Data.RTNCircle2Time6Step02AdjointSupport1.transverseLimit
  | 3 => Data.RTNCircle2Time6Step03AdjointSupport1.transverseLimit
  | 4 => Data.RTNCircle2Time6Step04AdjointSupport1.transverseLimit
  | 5 => Data.RTNCircle2Time6Step05AdjointSupport1.transverseLimit
  | 6 => Data.RTNCircle2Time6Step06AdjointSupport1.transverseLimit
  | 7 => Data.RTNCircle2Time6Step07AdjointSupport1.transverseLimit
  | 8 => Data.RTNCircle2Time6Step08AdjointSupport1.transverseLimit
  | 9 => Data.RTNCircle2Time6Step09AdjointSupport1.transverseLimit
  | 10 => Data.RTNCircle2Time6Step10AdjointSupport1.transverseLimit
  | _ => Data.RTNCircle2Time6Step11AdjointSupport1.transverseLimit
def boxInput : ℕ → ℚ
  | 0 => Data.RTNCircle2Time6Step00AdjointSupport1.boxInput
  | 1 => Data.RTNCircle2Time6Step01AdjointSupport1.boxInput
  | 2 => Data.RTNCircle2Time6Step02AdjointSupport1.boxInput
  | 3 => Data.RTNCircle2Time6Step03AdjointSupport1.boxInput
  | 4 => Data.RTNCircle2Time6Step04AdjointSupport1.boxInput
  | 5 => Data.RTNCircle2Time6Step05AdjointSupport1.boxInput
  | 6 => Data.RTNCircle2Time6Step06AdjointSupport1.boxInput
  | 7 => Data.RTNCircle2Time6Step07AdjointSupport1.boxInput
  | 8 => Data.RTNCircle2Time6Step08AdjointSupport1.boxInput
  | 9 => Data.RTNCircle2Time6Step09AdjointSupport1.boxInput
  | 10 => Data.RTNCircle2Time6Step10AdjointSupport1.boxInput
  | _ => Data.RTNCircle2Time6Step11AdjointSupport1.boxInput
def cylinderInput : ℕ → ℚ
  | 0 => Data.RTNCircle2Time6Step00AdjointSupport1.cylinderInput
  | 1 => Data.RTNCircle2Time6Step01AdjointSupport1.cylinderInput
  | 2 => Data.RTNCircle2Time6Step02AdjointSupport1.cylinderInput
  | 3 => Data.RTNCircle2Time6Step03AdjointSupport1.cylinderInput
  | 4 => Data.RTNCircle2Time6Step04AdjointSupport1.cylinderInput
  | 5 => Data.RTNCircle2Time6Step05AdjointSupport1.cylinderInput
  | 6 => Data.RTNCircle2Time6Step06AdjointSupport1.cylinderInput
  | 7 => Data.RTNCircle2Time6Step07AdjointSupport1.cylinderInput
  | 8 => Data.RTNCircle2Time6Step08AdjointSupport1.cylinderInput
  | 9 => Data.RTNCircle2Time6Step09AdjointSupport1.cylinderInput
  | 10 => Data.RTNCircle2Time6Step10AdjointSupport1.cylinderInput
  | _ => Data.RTNCircle2Time6Step11AdjointSupport1.cylinderInput
def joinCharge : ℕ → ℚ
  | 0 => (8521274077088761244390796047669/44601490397061246283071436545296723011960832000000)
  | 1 => (341006412557381056285334207061/1393796574908163946345982392040522594123776000000)
  | 2 => (292899127695358475128477294967/1393796574908163946345982392040522594123776000000)
  | 3 => (70135238349606349727499609441/174224571863520493293247799005065324265472000000)
  | 4 => (30018491675034910598404325109/87112285931760246646623899502532662132736000000)
  | 5 => (97634963125158696994369967303/174224571863520493293247799005065324265472000000)
  | 6 => (10640444560304743584176167428817/22300745198530623141535718272648361505980416000000)
  | 7 => (3203374741467295580163416647789/5575186299632655785383929568162090376495104000000)
  | 8 => (252726503810433808983223721893/696898287454081973172991196020261297061888000000)
  | 9 => (5880919604974467932058146839617/11150372599265311570767859136324180752990208000000)
  | _ => (487248473626246130316365776281673/713623846352979940529142984724747568191373312000000)
def initialCharge : ℚ := (6130741209215730140478445/5575186299632655785383929568162090376495104)
def terminalCharge : ℚ := (637560320855825485888019647/43556142965880123323311949751266331066368000000)
def terminalRow (i : Fin 13) : ℚ := if i = 1 then 1 else 0
def positionBound (cylinder : Bool) : ℚ :=
  if cylinder then (17387/25) else (33109/20)
def relativePositionBound (cylinder : Bool) : ℚ :=
  if cylinder then (17391/25) else (165561/100)
def totalCharge (supply : ℕ → ℚ) : ℚ :=
  initialCharge+(∑ j ∈ Finset.range 12, (1/20)*(supply j+charge j))+
    (∑ j ∈ Finset.range 11, joinCharge j)+terminalCharge

theorem supports_checked (j : ℕ) (hj : j < 12) :
    0 ≤ transverseLimit j ∧
    circle.bound (transversePolynomial circle (ell j)) (1/20) 0 ≤ (transverseLimit j)^2 ∧
    (if RTNCircle2Time6.on j = 0 then 0 else cylinderSupport circle (ell j) (1/20) 0 (transverseLimit j)) ≤ cylinderInput j ∧
    (∑ i, circle.bound (ell j i) (1/20) 0*RTNCircle2Time6.input j i) ≤ boxInput j := by
  interval_cases j
  · exact Data.RTNCircle2Time6Step00AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step01AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step02AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step03AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step04AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step05AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step06AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step07AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step08AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step09AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step10AdjointSupport1.checked
  · exact Data.RTNCircle2Time6Step11AdjointSupport1.checked

theorem initial_charge_checked :
    initialPairCharge circle (ell 0) (RTNCircle2Time6.steps 0).initialError 0 ≤ initialCharge := by
  decide +kernel

theorem joins_charge_checked (j : ℕ) (hj : j < 11) :
    joinPairCharge circle (RTNCircle2Time6.steps j).coefficients (ell j)
      (RTNCircle2Time6.steps (j+1)).coefficients (ell (j+1))
      (RTNCircle2Time6.steps j).error (1/20) 0 ≤ joinCharge j := by
  interval_cases j <;> decide +kernel

theorem terminal_charge_checked :
    terminalPairCharge circle (ell 11) terminalRow (RTNCircle2Time6.steps 11).error
      (1/20) 0 ≤ terminalCharge := by
  decide +kernel

theorem totals_checked (cylinder : Bool) :
    ApproachGate.radiusSI*totalCharge (if cylinder then cylinderInput else boxInput) ≤ positionBound cylinder := by
  cases cylinder <;> decide +kernel
theorem relative_totals_checked (cylinder : Bool) :
    ApproachGate.radiusSI*(totalCharge (if cylinder then cylinderInput else boxInput)+totalCharge (fun _ => 0)) ≤ relativePositionBound cylinder := by
  cases cylinder <;> decide +kernel
end GNC.MotorBurn.RTNAlongTrackAdjoint
