import GNC.Analysis.SphereRankOne
import GNC.Applications.OrbitalComparison.PointingCapDiskData.DiskHornerTime14Burn1200

/-! Generated proposal; exact constraint identities and physical bounds are
kernel checked. Compression is separate from the already checked full orbit
predictor. No omitted term or floating-point discrepancy is assumed zero. -/
namespace GNC.OrbitalComparison.PointingCapGeometryCompression
open ParameterPolynomial PointingCapCertificate PointingCapBurn SpatialBurn Set
open PointingCapDiskData.DiskHornerTime14Burn1200
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev data := PointingCapData.HornerTime14Burn1200.data

def candidate : PointingCapPolynomial.Vector := ![[⟨0,0,1,[0,0,(-376030351334893/34359738368),0,(6674464891358341/4398046511104),0,(-23066923920925687/281474976710656),0,(9125467779416761/4503599627370496),0,(-9899542466323/2251799813685248),0,(-1908440946036055/1152921504606846976),0,(2891185451569307/36893488147419103232)]⟩,⟨1,0,0,[0,0,0,(1295951002840575/137438953472),0,(-3456914930809797/4398046511104),0,(2207922681114305/70368744177664),0,(-1645175139942235/2251799813685248),0,(6419043080607563/576460752303423488),0,(-551882408000759/4611686018427387904)]⟩,⟨2,0,0,[0,0,0,0,0,0,0,0,(-10897265432322997/9007199254740992),0,(4729596993643709/36028797018963968),0,(-1081418242329241/144115188075855872),0,(1326793844989955/4611686018427387904)]⟩],[⟨0,0,1,[0,0,0,(1295951002840575/137438953472),0,(-3456914930809797/4398046511104),0,(17068195178101013/562949953421312),0,(-168112914144929065/288230376151711744),0,(9681086029394277/9223372036854775808),0,(97134726551895295/295147905179352825856)]⟩,⟨1,0,0,[0,0,(376030351334893/34359738368),0,(-6702683730900425/1099511627776),0,(373008344320703/1099511627776),0,(-2858851093244355/281474976710656),0,(6816631389849589/36028797018963968),0,(-2770490906698685/1152921504606846976),0,(6533353811621465/295147905179352825856)]⟩,⟨2,0,0,[0,0,0,0,0,0,0,(7935816944178999/4503599627370496),0,(-179198045868738743/576460752303423488),0,(433449241536877049/18446744073709551616),0,(-643867947073570831/590295810358705651712)]⟩],[⟨0,1,0,[0,0,(376030351334893/34359738368),0,(-3356045005373893/2199023255552),0,(5990494138630943/70368744177664),0,(-5728365845518351/2251799813685248),0,(6816702788860701/144115188075855872),0,(-1382695527977101/2305843009213693952),0,(6509254904530223/1180591620717411303424)]⟩]]
def remainder : PointingCapPolynomial.Vector := ![[⟨0,0,2,[0,0,0,0,0,0,(-2417771527213309/562949953421312),0,(6907848680818383/9007199254740992),0,(-2309339603298553/36028797018963968),0,(1943237665578471/576460752303423488),0,(-1157091132593279/9223372036854775808)]⟩,⟨1,0,1,[0,0,0,0,0,0,0,(4761490166507399/1125899906842624),0,(-5214162986781035/9007199254740992),0,(358273801858075/9007199254740992),0,(-8205016098499843/4611686018427387904)]⟩],[⟨0,0,2,[0,0,0,0,0,0,0,(-198395423604475/1125899906842624),0,(4593844751948009/576460752303423488),0,(-3111302792312263/18446744073709551616),0,(1159951469030001/590295810358705651712)]⟩,⟨1,0,1,[0,0,0,0,0,0,(-1611847684808873/562949953421312),0,(472614015553941/562949953421312),0,(-2854256244059181/36028797018963968),0,(5034705945008015/1152921504606846976),0,(-1527037197527629/9223372036854775808)]⟩],[⟨0,1,1,[0,0,0,0,0,0,(-1611847684808873/562949953421312),0,(4613152425999185/9007199254740992),0,(-6168082049846169/144115188075855872),0,(5188207788792523/2305843009213693952),0,(-3088076887173837/36893488147419103232)]⟩,⟨1,1,0,[0,0,0,0,0,0,0,(3967908472089499/2251799813685248),0,(-2431770098209259/9007199254740992),0,(2795919722301827/144115188075855872),0,(-254482231649579/288230376151711744)]⟩]]
def witness : PointingCapPolynomial.Vector := ![[⟨0,0,0,[0,0,0,0,0,0,(2417771527213309/562949953421312),0,(-6907848680818383/9007199254740992),0,(2309339603298553/36028797018963968),0,(-1943237665578471/576460752303423488),0,(1157091132593279/9223372036854775808)]⟩],[⟨0,0,0,[0,0,0,0,0,0,0,(198395423604475/1125899906842624),0,(-4593844751948009/576460752303423488),0,(3111302792312263/18446744073709551616),0,(-1159951469030001/590295810358705651712)]⟩],[]]

def plane : DiskPolynomial.Certificate 2 where
  left := { coefficients := ![[],[]], bound := 0 }
  right := { coefficients := ![[],[]], bound := 0 }
  count := 2
  higher := ![{ u := 0, v := 0, c := 2, curve := { coefficients := ![[0,0,0,0,0,0,(-2417771527213309/562949953421312),0,(6907848680818383/9007199254740992),0,(-2309339603298553/36028797018963968),0,(1943237665578471/576460752303423488),0,(-1157091132593279/9223372036854775808)],[0,0,0,0,0,0,0,(-198395423604475/1125899906842624),0,(4593844751948009/576460752303423488),0,(-3111302792312263/18446744073709551616),0,(1159951469030001/590295810358705651712)]], bound := (2171654192504835429257601/604462909807314587353088) }, monomialBound := 1 },
    { u := 1, v := 0, c := 1, curve := { coefficients := ![[0,0,0,0,0,0,0,(4761490166507399/1125899906842624),0,(-5214162986781035/9007199254740992),0,(358273801858075/9007199254740992),0,(-8205016098499843/4611686018427387904)],[0,0,0,0,0,0,(-1611847684808873/562949953421312),0,(472614015553941/562949953421312),0,(-2854256244059181/36028797018963968),0,(5034705945008015/1152921504606846976),0,(-1527037197527629/9223372036854775808)]], bound := (5130049592326320861799129/1208925819614629174706176) }, monomialBound := (1/10) }]
def normal : DiskPolynomial.Certificate 1 where
  left := { coefficients := ![[]], bound := 0 }
  right := { coefficients := ![[]], bound := 0 }
  count := 2
  higher := ![{ u := 0, v := 1, c := 1, curve := { coefficients := ![[0,0,0,0,0,0,(-1611847684808873/562949953421312),0,(4613152425999185/9007199254740992),0,(-6168082049846169/144115188075855872),0,(5188207788792523/2305843009213693952),0,(-3088076887173837/36893488147419103232)]], bound := (88237683291768751901/36893488147419103232) }, monomialBound := (1/10) },
    { u := 1, v := 1, c := 0, curve := { coefficients := ![[0,0,0,0,0,0,0,(3967908472089499/2251799813685248),0,(-2431770098209259/9007199254740992),0,(2795919722301827/144115188075855872),0,(-254482231649579/288230376151711744)]], bound := (435412998497713659/288230376151711744) }, monomialBound := (1/200) }]
def planeBound : ℚ := (1064312952723034560083178691/478746713825589299475392757760)
def normalBound : ℚ := (3213898390892284340017/367090207066820077158400)
def compressionError : ℚ := (10920115849126005371929/1208925819614629174706176)
def physicalError : ℚ := 2909/10000000
def totalError : ℚ := compressionError+physicalError
/-- Upward display rounding to nanometres; the exact bound is totalError. -/
def displayError : ℚ := (⌈1000000000*totalError⌉:ℚ)/1000000000

theorem constraint_identity : ∀ i, zero (subtract (subtract (data.q i) (candidate i))
    (add (remainder i) (multiply PointingCapPolynomial.constraint (witness i)))) := by
  decide +kernel
theorem plane_valid : plane.Valid (fun i => remainder i.castSucc)
    data.sigma (PointingCapDisk.depth data.sigma) planeBound := by
  constructor <;> decide +kernel
theorem normal_valid : normal.Valid (fun _ => remainder 2)
    data.sigma (PointingCapDisk.depth data.sigma) normalBound := by
  constructor <;> decide +kernel
theorem bounds_nonnegative : 0≤planeBound ∧ 0≤normalBound ∧ 0≤compressionError := by
  decide +kernel
theorem squared_bound : planeBound^2+normalBound^2≤compressionError^2 := by decide +kernel
theorem display_value : displayError=(9323809/1000000000) := by decide +kernel
theorem total_below_display : totalError≤displayError := by decide +kernel
theorem meets_centimetre : displayError<1/100 := by decide +kernel

/-- The stored polynomial really uses only u, v, c and u^2, and its normal
coordinate is linear in v. These are checked coefficients, not a producer label. -/
theorem features : ∀ j, ∀ a ∈ candidate j,
    (a.u=1 ∧ a.v=0 ∧ a.c=0) ∨ (a.u=0 ∧ a.v=1 ∧ a.c=0) ∨
    (a.u=0 ∧ a.v=0 ∧ a.c=1) ∨ (a.u=2 ∧ a.v=0 ∧ a.c=0) := by decide +kernel
theorem planar_features : ∀ j : Fin 2, ∀ a ∈ candidate j.castSucc, a.v=0 := by decide +kernel
theorem normal_linear : ∀ a ∈ candidate 2, a.u=0 ∧ a.v=1 ∧ a.c=0 := by decide +kernel

noncomputable section

/-- Time coefficients are prepared separately from a pointing query. -/
def coefficient (i : Fin 3) (k : ℕ) (t : ℝ) : ℝ :=
  PolynomialOrder.value ((candidate i).getD k ⟨0,0,0,[]⟩).time t

def query (x : Fin 3 → ℝ) (t : ℝ) : Fin 3 → Planning.FlopKernel.Value ℝ :=
  ![SphereRankOne.queryComponent (x 0) (x 2)
      (coefficient 0 1 t) (coefficient 0 0 t) (coefficient 0 2 t),
    SphereRankOne.queryComponent (x 0) (x 2)
      (coefficient 1 1 t) (coefficient 1 0 t) (coefficient 1 2 t),
    Planning.FlopKernel.mul (Planning.FlopKernel.input (x 1))
      (Planning.FlopKernel.input (coefficient 2 0 t))]

theorem query_matches (x : Fin 3 → ℝ) (t : ℝ) :
    WithLp.toLp 2 (fun i => (query x t i).value)=
      PointingCapPolynomial.vectorValue candidate x t := by
  ext i
  fin_cases i <;>
    simp [query,coefficient,candidate,SphereRankOne.queryComponent_value,
      Planning.FlopKernel.mul,Planning.FlopKernel.input,
      PointingCapPolynomial.vectorValue,pack_eq,value,termValue,monomial] <;> ring

theorem query_flops (x : Fin 3 → ℝ) (t : ℝ) :
    (∑ i, (query x t i).flops)=11 := by
  rw [Fin.sum_univ_three]
  rfl

theorem compression_bound {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖data.displacement x t-PointingCapPolynomial.vectorValue candidate x t‖≤
      (compressionError:ℝ) := by
  have hσ : (0:ℝ)≤data.sigma := by change 0≤((1/10:ℚ):ℝ); norm_num
  have hs : (data.sigma:ℝ)^2<1 := by change ((1/10:ℚ):ℝ)^2<1; norm_num
  have hc := (parameter_bounds hσ hs hx).2.2
  have hc' : |x 2|≤(PointingCapDisk.depth data.sigma:ℝ) := by
    simpa only [PointingCapDisk.depth,Rat.cast_div,Rat.cast_pow,Rat.cast_sub,Rat.cast_ofNat] using hc
  have h := SphereRankOne.split_bound remainder plane normal plane_valid normal_valid
    (by decide +kernel) bounds_nonnegative.1 bounds_nonnegative.2.1 bounds_nonnegative.2.2
    squared_bound hx.2.2.2 hc' ht
  rw [PointingCapDisk.vector_value_eq] at h
  have hid : PointingCapPolynomial.vectorValue
      (PointingCapPolynomial.difference data.q candidate) x t=
      PointingCapPolynomial.vectorValue remainder x t := by
    ext i
    fin_cases i <;>
      simpa only [PointingCapPolynomial.vectorValue,PointingCapPolynomial.difference,pack_eq,
        value_subtract] using
        (PointingCapPolynomial.reduced_residual _ _ _ (constraint_identity _) hx t)
  rw [←hid,PointingCapPolynomial.vector_difference] at h
  exact h

def position (x : Fin 3 → ℝ) (t : ℝ) : E3 :=
  PointingCapFrame.reference (data.alpha:ℝ) t+
    PointingCapFrame.turn (data.alpha:ℝ) t (PointingCapPolynomial.vectorValue candidate x t)

/-- Full inverse-square physical error at EVERY time and EVERY admitted
direction. The physical solution is not replaced by a sampled numerical truth. -/
theorem physical_bound {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    (X : Motion (data.alpha:ℝ) (direction x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-position x t‖≤(displayError:ℝ) := by
  have hp := (bounds.certifies data PointingCapData.HornerTime14Burn1200.valid
    (models.refinedBounds_sound original PointingCapData.HornerTime14Burn1200.valid valid)
      checks hx X t ht).1
  have hl : (bounds.positionError data:ℝ)≤physicalError := by exact_mod_cast position_limit
  have he : ‖data.position x t-position x t‖≤(compressionError:ℝ) := by
    simpa only [Data.position,PointingCapFrame.position,position,add_sub_add_left_eq_sub,
      ←map_sub,PointingCapFrame.turn_norm] using compression_bound hx ht
  have ht' := norm_add_le (X.p t-data.position x t) (data.position x t-position x t)
  rw [sub_add_sub_cancel] at ht'
  have h := ht'.trans (add_le_add (hp.trans hl) he)
  have hd : (totalError:ℝ)≤displayError := by exact_mod_cast total_below_display
  apply le_trans _ hd
  simpa only [totalError,Rat.cast_add,add_comm] using h

theorem physical_prediction {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x) :
    ∃ X : Motion (data.alpha:ℝ) (direction x), ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-position x t‖≤(displayError:ℝ) :=
  ⟨data.trajectory PointingCapData.HornerTime14Burn1200.valid x hx,fun _ ht => physical_bound hx _ ht⟩

/-- Connect the counted real-arithmetic query to the actual physical error.
Floating-point execution and construction of the direction input are separate. -/
theorem query_physical_bound {x : Fin 3 → ℝ} (hx : Admissible (data.sigma:ℝ) x)
    (X : Motion (data.alpha:ℝ) (direction x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖X.p t-(PointingCapFrame.reference (data.alpha:ℝ) t+
      PointingCapFrame.turn (data.alpha:ℝ) t
        (WithLp.toLp 2 (fun i => (query x t i).value)))‖≤(displayError:ℝ) := by
  rw [query_matches]
  exact physical_bound hx X ht

end
end GNC.OrbitalComparison.PointingCapGeometryCompression
