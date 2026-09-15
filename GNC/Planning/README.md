# Verified reference geometry

[Dubins.lean](Dubins.lean) defines real-valued arc and line propagation and
proves its derivatives and unit-speed identity.
[DubinsPolynomial.lean](DubinsPolynomial.lean) adds:

- An explicit Hermite seed with eight proved endpoint conditions.
- Offset derivatives through fourth order in nominal distance.
- A continuous regularity bound for the symmetric zero-junction-curvature
  seed, and a bound preserved by positive diagonal footprint scaling.
- Exact metric correction, physical arc-length derivatives through third
  order, constant-speed acceleration and jerk, and coordinated bank rate.

[PolynomialKernel.lean](PolynomialKernel.lean) supplies executable coefficient
generation, Horner evaluation, differentiation and distance-scaled jets over
exact rationals. Lean proves that the algorithms agree with mathlib polynomial
evaluation and derivatives **for every input and derivative order**, that
rational evaluation commutes with embedding in the reals, and that the
symmetric seed retains its regularity bound throughout a segment. In
particular, `physicalJet_derivative` proves actual derivatives with respect
to nominal distance; it includes the powers of segment length needed for
correct scaling.

[Hermite.lean](Hermite.lean) extends the seed to **arbitrary endpoint values
and first, second and third derivatives**. Its explicit septic solver runs
over exact rationals without a numerical matrix solve. `normalized_start`
and `normalized_finish` prove all eight constraints; `normalized_recover`
and `normalized_unique` prove uniqueness among all eight-coefficient
polynomials. `physical_start`, `physical_finish` and `physical_unique`
include the interval-length scaling. `physicalJet_cast` and
`physicalJet_derivative` connect exact execution to actual real derivatives
at every order. These results hold for arbitrary nonzero lengths; the CLI
requires a positive length. Arbitrary endpoint data do not automatically
inherit the symmetric seed's geometric regularity bound.

Run the exact evaluator in the pinned environment:

```sh
nix develop --command lake build
nix develop --command lake env lean --run GNC/Tools/Planner.lean -1/4 -1/4 10 5 4
nix develop --command python scripts/check_planner.py
```

The five arguments are initial/final prescribed second derivatives, positive
segment length, nominal distance, and highest derivative order (0–32 in this
CLI; the theorems cover every order). Numbers are
integers or exact fractions. The example evaluates a 10 m segment at 5 m:
the offset is exactly `-75/64` m and its first derivative is zero. The JSON
reports normalized coefficients and physical nominal-distance derivatives.
The CLI parser, output serialization, and machine runtime have not been
formally verified. They are exercised by regression checks, including a
comparison against all four stored figure-eight segments.

The general solver accepts two comma-separated endpoint jets in physical
nominal distance:

```sh
nix develop --command lake env lean --run GNC/Tools/Planner.lean hermite 0,0,-1/4,0 0,0,-1/4,0 10 5 4
```

The endpoint entries are value, first derivative, second derivative, third
derivative. This example exactly reproduces the earlier seed. The general
mode returns coefficients in normalized distance `q/L`, whereas the pinned
Modelica `Polynomials.hermiteCoefficients` returns coefficients in `q`.
Dividing coefficient `j` by `L^j` converts the former to the latter. Interface
tests reconstruct independently chosen polynomials on unequal interval
lengths and compare both CLI modes for the stored figure-eight segments.

The geometry remains a Lean specification over the reals, checked with
released mathlib; the polynomial kernel is also executable over rationals.
Neither supplies certified floating-point rounding or trigonometric evaluation.
The figure-eight experiment in the companion papers repository
uses numerical counterparts and checks them against compiled scalar Modelica.
The explicit seed coefficients follow the Lean definition; an independent
Hermite system solve checks them numerically.

Not yet proved: all six Dubins candidate formulas and global shortest-path
selection, the general joint polynomial optimizer, global piecewise C3/C5
gluing, the curvature second-derivative and aerodynamic feedforward formulas,
compiler semantics, and floating-point error enclosures. Optimal path-family
selection is piecewise smooth; automatic differentiation inside a family
does not make the switching map globally differentiable.
The Modelica Hermite solver supports arbitrary endpoint derivative counts;
the new Lean construction proves the four-derivative (septic) case.

For a future Rumoca-to-Lean pipeline, retain this Lean kernel as the reference
specification and use a separate adapter for generated Modelica equations.
For each supported pure function, prove that evaluating the translated
function agrees with this specification on its declared input domain. This
can be a checked proof for each translation; it need not wait for a verified
general compiler. The adapter must also connect the source Modelica semantics
to the translated function, or explicitly leave that as a trust boundary.
Type checking generated Lean alone does not certify the translation.
Differential-equation models additionally need initialization, event,
algebraic-loop and numerical-evaluation semantics. The handwritten library
and its theorems can remain stable as that translation support grows.
`Hermite.physical_unique` supplies a concrete route for that adapter: prove
the translated eight-coefficient output satisfies the scaled endpoint
equations, then invoke uniqueness. See the
[library verification contract](../../docs/VERIFICATION.md) for the precise
claim supported by the build.
