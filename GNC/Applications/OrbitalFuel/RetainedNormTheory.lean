import GNC.Analysis.PolynomialAffine

/-! Certificates for the polynomial retained-response proposal. Soundness
here concerns this explicit polynomial family. Connecting it to the true
reference-dependent response requires the separate coefficient/error proof.
-/
namespace GNC.Applications.OrbitalFuel.RetainedNorm
open GNC GNC.PolynomialAffine GNC.ThrustSupport

def kappa : ℚ := 12499881009/12500000000
def lengthScale : ℚ := 149597870700
def speedUpper : ℚ := 29784691831696803791952916064574541/10^30+1/10^25
def positionBound : ℚ := 10123000
def velocityBound : ℚ := 128/25
def scale : Fin 2 → ℚ := ![lengthScale,speedUpper]
def bound : Fin 2 → ℚ := ![positionBound,velocityBound]

structure Piece where
  start : ℚ
  finish : ℚ
  referenceStep : Fin 32
  columns : Fin 2 → Fin 4 → VectorPolynomial
  certificates : Fin 2 → Certificate

def Piece.offset (p : Piece) : ℚ := p.referenceStep.val*(3/160)

def Piece.Valid (p : Piece) : Prop :=
  p.start ≤ p.finish ∧ p.offset ≤ p.start ∧ p.finish ≤ p.offset+3/160 ∧ ∀ j,
    p.offset+(p.certificates j).center-(p.certificates j).radius = p.start ∧
    p.offset+(p.certificates j).center+(p.certificates j).radius = p.finish ∧
    0 ≤ scale j ∧ (p.certificates j).resultRadius*scale j ≤ bound j ∧
    (p.certificates j).Valid kappa
      (plus (p.columns j 0) (p.columns j 3)) (p.columns j 1) (p.columns j 2) (p.columns j 3)

instance (p : Piece) : Decidable p.Valid := by unfold Piece.Valid; infer_instance

noncomputable def Piece.response (p : Piece) (j : Fin 2) (t : ℝ) (q : Vec3) : Vec3 :=
  value (p.columns j 0) (t-(p.offset:ℝ))+
    q 0 • value (p.columns j 1) (t-(p.offset:ℝ))+
    q 1 • value (p.columns j 2) (t-(p.offset:ℝ))+
    q 2 • value (p.columns j 3) (t-(p.offset:ℝ))

theorem Piece.enclosure (p : Piece) (hp : p.Valid) (j : Fin 2) {t : ℝ}
    (ht : t ∈ Set.Icc (p.start:ℝ) (p.finish:ℝ)) (q : Vec3)
    (hq : q ∈ Cap pointingAxis (kappa:ℝ)) :
    GNC.enorm (p.response j t q)*(scale j:ℝ) ≤ (bound j:ℝ) := by
  obtain ⟨hl,hu,hscale,hbound,hcert⟩ := hp.2.2.2 j
  have hl' : (p.offset:ℝ)+(p.certificates j).center-(p.certificates j).radius =
      (p.start:ℝ) := by exact_mod_cast hl
  have hu' : (p.offset:ℝ)+(p.certificates j).center+(p.certificates j).radius =
      (p.finish:ℝ) := by exact_mod_cast hu
  have htime : |(t-(p.offset:ℝ))-(p.certificates j).center| ≤
      ((p.certificates j).radius:ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2]
  have hb := affine_certificate_sound (p.certificates j) kappa (p.columns j 0)
    (p.columns j 1) (p.columns j 2) (p.columns j 3) hcert htime q hq
  exact (mul_le_mul_of_nonneg_right hb (show (0:ℝ) ≤ (scale j:ℝ) by exact_mod_cast hscale)).trans
    (by exact_mod_cast hbound)

theorem Piece.reference_interval (p : Piece) (hp : p.Valid) {t : ℝ}
    (ht : t ∈ Set.Icc (p.start:ℝ) (p.finish:ℝ)) :
    t-(p.offset:ℝ) ∈ Set.Icc (0:ℝ) (3/160) := by
  have hl : (p.offset:ℝ) ≤ (p.start:ℝ) := by exact_mod_cast hp.2.1
  have hu : (p.finish:ℝ) ≤ ((p.offset+3/160:ℚ):ℝ) := by exact_mod_cast hp.2.2.1
  push_cast at hu
  constructor <;> linarith [ht.1,ht.2]

/-- An ordered chain of closed intervals covers its entire horizon. The
induction also handles equality at a command or reference-cell boundary. -/
theorem interval_chain_covers {N : ℕ} (start finish : Fin (N+1) → ℝ)
    (hjoin : ∀ i : Fin N, finish i.castSucc = start i.succ) {t : ℝ}
    (ht : start 0 ≤ t ∧ t ≤ finish (Fin.last N)) :
    ∃ i, start i ≤ t ∧ t ≤ finish i := by
  induction N with
  | zero => exact ⟨0, ht⟩
  | succ N ih =>
    by_cases hlast : start (Fin.last (N+1)) ≤ t
    · exact ⟨Fin.last (N+1), hlast, ht.2⟩
    · have hleft : start 0 ≤ t ∧ t ≤ finish (Fin.last N).castSucc := by
        refine ⟨ht.1, ?_⟩
        rw [hjoin (Fin.last N)]
        exact le_of_lt (lt_of_not_ge hlast)
      obtain ⟨i, hi⟩ := ih (fun i => start i.castSucc) (fun i => finish i.castSucc)
        (fun i => hjoin i.castSucc) hleft
      exact ⟨i.castSucc, hi⟩

end GNC.Applications.OrbitalFuel.RetainedNorm
