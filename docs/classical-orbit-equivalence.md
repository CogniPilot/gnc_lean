# HCW, TH/YA, and the retained SE₂(3) coast error equations

These are exact equivalence theorems for **linear variational dynamics**.
They do not identify finite-separation nonlinear two-body motion with HCW
or TH. The nonlinear gravity residual in the orbital log-error theorem
remains present outside the retained model.

## Assumptions and conventions

- Unforced two-body reference, with semilatus rectum `p > 0`, angular
  momentum magnitude `h > 0`, `0 ≤ e < 1`, and `h² = μ p`. These imply `μ > 0`.
- A differentiable, unwrapped true anomaly `f(t)` satisfying the Kepler
  clock `f' = h k²/p²`, where `k = 1 + e cos f` and radius `r = p/k`.
  The global STM identification theorems take this clock and the retained
  fundamental solution on the real line; every finite interval is included.
- The reference axes are radial, transverse, normal (RTN), rotating at
  `w = f'`; the radial gradient is `G = diag(2μ/r³, −μ/r³, −μ/r³)`.
  The frame acceleration is retained, including on eccentric orbits.
- Thrust is zero for the classical specialization. The six-dimensional
  state is the translational block of the retained SE₂(3) error, in position
  then velocity order. Attitude is not an extra forcing of that block at
  first order during coast.
- HCW additionally requires a circular reference. Its frequency is positive,
  its physical radius is constant, and `n² = μ/r³`.

## The two required coordinate changes

The log-system velocity is inertial velocity difference expressed in RTN.
It is **not** the derivative of RTN position. If `W = skew(0,0,w)`, define

```
S(t) = [ I   0 ]             (x, v_rotated) ↦ (x, x_dot)
       [−W   I ]
```

The exact transformed generator is

```
A_log = [−W  I ]       A_classical = [      0            I ]
        [ G −W ]                     [ G−W²−W_dot       −2W ]

S_dot + S A_log = A_classical S.
```

[ClassicalOrbitEquivalence](../GNC/Dynamics/ClassicalOrbitEquivalence.lean)
proves both directions at the solution level, explicit inverses, and the
STM transformation at both endpoints. `hcw_generator` recovers precisely
the usual HCW blocks under `μ/r³ = n²` and zero frame acceleration.

TH/YA also uses scaled position and true-anomaly derivatives. Write
`kp = dk/df = −e sin f` and define

```
C(t) = [ k I      0   ]      (x, x_dot) ↦ (k x, d(k x)/df)
       [ kp I   (k/w) I ]
```

[KeplerAnomaly](../GNC/Dynamics/KeplerAnomaly.lean) derives

```
μ/r³ = w²/k,     w_dot = 2 w² kp/k,
k_dot = w kp,    kp_dot = w(1−k).
```

These identities, rather than a frozen-rate assumption, give the canonical
TH equations in true anomaly:

```
u_radial''     = (3/k) u_radial + 2 u_transverse'
u_transverse'' = −2 u_radial'
u_normal''     = −u_normal.
```

The clock factor `w` remains when these equations are written in physical
time. Both `S` and `C` are proved invertible in the stated domain.

## The explicit YA solution is checked

[YamanakaAnkersen](../GNC/Dynamics/YamanakaAnkersen.lean) defines and
differentiates the explicit four planar fundamental columns, including the
secular column, plus the harmonic normal block. These are the YA columns
with an equivalent ordering and sign/scaling convention.

With `s = sin f`, `c = cos f`, and `J' = 1/k²`, the planar matrix is

```
[ k s             k c              2−3 e k J s                       0 ]
[ (1+k)c         −(1+k)s           −3 k² J                            1 ]
[ c+e(c²−s²)     −s−2 e s c        −3e[J(c+e(c²−s²))+s/k]             0 ]
[−2 k s           e−2 k c          −3+6 e k J s                       0 ].
```

The proof establishes `F' = A_TH F`, `det F_planar = e²−1`, and a unit
determinant for the normal block. Thus nonsingularity is derived from the
eccentricity assumptions; it is not supplied as an unverified premise.
The normalized propagator is `F(f) F(f₀)⁻¹` and equals the identity at `f₀`.

`secular_along_kepler` proves

```
J(f(t)) = h/p² · (t−t₀),       J(f(t₀)) = 0.
```

Consequently there is no remaining numerical quadrature in this YA formula
when the reference phase is known. Determining phase from time is still
the ordinary Kepler-reference problem; the theorem does not eliminate it.

## End-to-end STM identities

Let `T(t) = C(t) S(t)`. Let `P` reorder states from position/velocity blocks
to `(radial, transverse, radial derivative, transverse derivative, normal,
normal derivative)`, the ordering of the displayed YA blocks. Then

```
Φ_log(t,t₀) = T(t)⁻¹ P⁻¹ Φ_YA(f(t),f(t₀)) P T(t₀).
```

This is `ClassicalOrbitSTM.kepler_stm_formula`, proved by differentiation,
normalization, the verified YA basis, and uniqueness from mathlib's ODE
theory. `kepler_stm_equivalence` gives the corresponding forward identity.
`coast_log_block` connects its generator to the paper's actual
`OrbitalNearAffine.linearPart`, using the inverse-square gradient theorem.

For `e = 0`, `k = 1`, `kp = 0`, and `f(t) = n t`, `hcw_ya_equivalence`
identifies the normalized physical-time HCW STM with this same explicit
YA solution after velocity scaling by `1/n` and the fixed state permutation.
HCW is therefore the circular specialization of TH/YA, not a competing
approximation to its circular variational dynamics.

All main equivalence statements are in
[ClassicalOrbitSTM](../GNC/Dynamics/ClassicalOrbitSTM.lean), exported through
`GNC.Core` and included in the full library audit. No floating-point
tolerances, numerical integrations, new axioms, or admitted steps enter
these proofs. The Python/SciPy implementation remains a separate executable;
this does not assert a verified translation of that program.

Reproduce with the library's pinned flake and Lake cache:

```sh
nix develop --command lake build GNC.Dynamics.ClassicalOrbitSTM
nix develop --command python scripts/verify.py
```
