import GNC.Dynamics.RadialThrustReduction
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-! An elliptic radial solution of the full constant-radial-acceleration
energy equation. The lattice invariants and phase are explicit hypotheses:
this file does not construct a lattice/phase for every physical initial
condition, prove reality/positivity, invert time, or reconstruct the angle. -/
noncomputable section
namespace GNC.RadialThrust

def ellipticRadius (L : PeriodPair) (a e z : ℂ) : ℂ :=
  (2/a)*(L.weierstrassP z-e/6)

def ellipticRadiusRate (L : PeriodPair) (a z : ℂ) : ℂ :=
  (2/a)*L.derivWeierstrassP z

theorem ellipticRadius_derivative (L : PeriodPair) (a e z : ℂ)
    (hz : z ∉ L.lattice) :
    HasDerivAt (ellipticRadius L a e) (ellipticRadiusRate L a z) z := by
  have hd := (L.differentiableOn_weierstrassP.differentiableAt
    (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  rw [L.deriv_weierstrassP] at hd
  exact (hd.sub_const (e/6)).const_mul (2/a)

/-- The actual mathlib Weierstrass function satisfies the full radial cubic;
its defining differential equation is reused from mathlib. -/
theorem ellipticRadius_energy (L : PeriodPair) (a e mu h2 z : ℂ)
    (ha : a ≠ 0) (hz : z ∉ L.lattice)
    (hg2 : L.g₂ = e^2/3-a*mu)
    (hg3 : L.g₃ = -e^3/27+a*mu*e/6+a^2*h2/4) :
    ellipticRadiusRate L a z ^ 2 =
      2*a*ellipticRadius L a e z ^ 3 + 2*e*ellipticRadius L a e z ^ 2 +
        2*mu*ellipticRadius L a e z-h2 := by
  have he := L.derivWeierstrassP_sq z hz
  rw [hg2, hg3] at he
  unfold ellipticRadius ellipticRadiusRate
  rw [mul_pow, he]
  field_simp
  ring

/-- After `dt/dτ = r`, radial velocity is `r'/r` and has exactly the
original inverse-square-plus-constant-radial-thrust energy. -/
theorem ellipticRadius_physical_energy (L : PeriodPair) (a e mu h2 z : ℂ)
    (ha : a ≠ 0) (hz : z ∉ L.lattice)
    (hg2 : L.g₂ = e^2/3-a*mu)
    (hg3 : L.g₃ = -e^3/27+a*mu*e/6+a^2*h2/4)
    (hr : ellipticRadius L a e z ≠ 0) :
    (ellipticRadiusRate L a z / ellipticRadius L a e z)^2/2 +
      h2/(2*ellipticRadius L a e z^2) - mu/ellipticRadius L a e z -
        a*ellipticRadius L a e z = e := by
  have he := ellipticRadius_energy L a e mu h2 z ha hz hg2 hg3
  field_simp
  linear_combination he

end GNC.RadialThrust
