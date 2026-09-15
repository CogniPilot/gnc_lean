import GNC.Applications.OrbitalComparison.PointingCapClearance
import GNC.Applications.OrbitalComparison.PointingCapData.HornerTime12Burn1200

/-! Generated weighted-square proposal. All identities and physical bounds
are checked by Lean. The floating-point multiplier search is untrusted. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace GNC.OrbitalComparison.PointingCapSupportData.HornerTime12Burn1200
open PointingCapSupport PointingCapClearance PointingCapBurn PointingCapCertificate
open PointingCapData.HornerTime12Burn1200
def certificate : Certificate where
  time := 1
  upper := (149248614830600683057567033220466022199583282308539307500102013659436147264241001525347134751634405530876623153/176177588853206076443036689702729017278986676848388103229061826163560053559536615501894320836868493038059520)
  depth := (3029908352124674147599/604462909807314587353088)
  depthMultiplier := (5971653361685743/68719476736)
  sphereMultiplier := [⟨0,0,0,[(-5642362560993407/137438953472)]⟩]
  squares := [((59163038827084032379091/1441151880758558720),[⟨0,0,0,[(-17906533989840592289961/473304310616672259032728)]⟩,⟨0,0,1,[(7258356145496959539/473304310616672259032728)]⟩,⟨0,1,0,[(-871334961458726476/59163038827084032379091)]⟩,⟨1,0,0,[1]⟩]),((224021798852346319014985656497183943624137031441/5456827179330802379845826065600116718305280),[⟨0,0,0,[(-20736949605301622279734250632405784889990587632/224021798852346319014985656497183943624137031441)]⟩,⟨0,0,1,[(5220277378265860096591115033552522678296336/224021798852346319014985656497183943624137031441)]⟩,⟨0,1,0,[1]⟩]),((848264234755831204833284941847251230595540703522363316260094580836763453/20662363951806363459139815666090882270118568455609203632287021793280),[⟨0,0,0,[(-4251977826918409753461811938785578813339088950072252130261133945531169/848264234755831204833284941847251230595540703522363316260094580836763453)]⟩,⟨0,0,1,[1]⟩])]
  diskSquares := []
def witness : Fin 3 → ℚ := ![(179116402005904457728/4734231800194693552733),(438231470698011820032/4734231800194693552733),(23730634650096678074/4734231800194693552733)]
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
theorem display_values : displayLower=(847145577/1000000) ∧
    displayUpper=(847151817/1000000) := by decide +kernel
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
end GNC.OrbitalComparison.PointingCapSupportData.HornerTime12Burn1200
