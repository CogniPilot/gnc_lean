import GNC.Applications.OrbitalComparison.PointingCapClearance
import GNC.Applications.OrbitalComparison.PointingCapData.HornerTaylor4Time12Burn1200

/-! Generated weighted-square proposal. All identities and physical bounds
are checked by Lean. The floating-point multiplier search is untrusted. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace GNC.OrbitalComparison.PointingCapSupportData.HornerTaylor4Time12Burn1200
open PointingCapSupport PointingCapClearance PointingCapBurn PointingCapCertificate
open PointingCapData.HornerTaylor4Time12Burn1200
def certificate : Certificate where
  time := 1
  upper := (2240523278642969102544561506178169872473418938846270902696970014559559343819/2644782604020851390465092203188939925855565671571838397435766485129625600)
  depth := (3029908352124674147599/604462909807314587353088)
  depthMultiplier := 0
  sphereMultiplier := []
  squares := [((302914759836337879016496707/7378697629483820646400),[⟨0,0,0,[(-11460158526758313480469296/302914759836337879016496707)]⟩,⟨0,1,0,[(-4461235002668679567360/302914759836337879016496707)]⟩,⟨1,0,0,[1]⟩]),((91759329441000854146219957551860316383714385720238249/2235116420340047150850030854661774136044211404800),[⟨0,0,0,[(-8493843896412050548887245694031019316200631939758528/91759329441000854146219957551860316383714385720238249)]⟩,⟨0,1,0,[1]⟩])]
  diskSquares := [((47994775378832679953853/73786976294838206464),[⟨0,0,0,[(-7742246555196756848/15998258459610893317951)]⟩,⟨1,0,0,[1]⟩]),((47994775378832679953853/73786976294838206464),[⟨0,0,0,[(-11764612695317543232/15998258459610893317951)]⟩,⟨0,1,0,[1]⟩]),((201333043040724388540756696006221620469561821/4611184053585952286599226466240292716544),[⟨0,0,0,[1]⟩])]
def witness : Fin 3 → ℚ := ![(89558201140391182336/2367115900096764709461),(219115735280286433280/2367115900096764709461),(11865317323884205226/2367115900096764709461)]
def sample : ℚ := ParameterPolynomial.rationalValue (projection data) witness 1
def lower : ℚ := sample-data.positionError
def upper : ℚ := certificate.upper+data.positionError
/-- Metres rounded outwards to micrometres for display only. -/
def displayLower : ℚ := (⌊1000000*lower⌋:ℚ)/1000000
def displayUpper : ℚ := (⌈1000000*upper⌉:ℚ)/1000000
theorem checked : certificate.Valid (projection data) data.sigma := by decide +kernel
theorem witness_valid : Admissible (data.sigma:ℝ) (fun i => (witness i:ℝ)) := by
  norm_num [Admissible,witness,data,Matrix.cons_val_two]
theorem optimization_gap : certificate.upper-sample < 1/1000000 := by decide +kernel
theorem display_encloses : displayLower≤lower ∧ upper≤displayUpper := by decide +kernel
theorem display_values : displayLower=(211786039/250000) ∧
    displayUpper=(847152589/1000000) := by decide +kernel
theorem display_width : displayUpper-displayLower<1/100 := by decide +kernel
theorem support_interval :
    (lower:ℝ)≤support data ∧ support data≤(upper:ℝ) := by
  simpa only [lower,upper,sample,Rat.cast_sub,Rat.cast_add] using
    physical_support_bounds data valid rfl certificate checked rfl witness witness_valid
theorem support_display :
    (displayLower:ℝ)≤support data ∧ support data≤(displayUpper:ℝ) := by
  have hl : (displayLower:ℝ)≤(lower:ℝ) := by exact_mod_cast display_encloses.1
  have hu : (upper:ℝ)≤(displayUpper:ℝ) := by exact_mod_cast display_encloses.2
  exact ⟨hl.trans support_interval.1,support_interval.2.trans hu⟩
end GNC.OrbitalComparison.PointingCapSupportData.HornerTaylor4Time12Burn1200
