# GNC library

All project Lean sources live here. The mathematical library includes both
reusable results and every paper's application proofs. `import GNC.All`
exports the complete development; `import GNC.Core` selects the general
mathematics. Every theorem is kernel-checked under its stated hypotheses; the
[verification contract](../docs/VERIFICATION.md) defines the scope of that
claim and its application/runtime boundaries. The supported publication wording is:

> GNC's mathematical theorems are fully formally verified in Lean, under
> their stated assumptions.

Attach a matching dated verification record when using this claim.
Build and audit the library independently with:

```sh
nix develop --command lake build Verification
```

For the release claim, run `nix develop --command python scripts/verify.py`
from the repository root. This builds all mathematical library sources with Lake's
incremental cache, audits the checked declarations and writes a source-hashed
report. Unchanged proofs are reused from `.lake/build`. Add `--fresh` for an
explicit isolated rebuild; its successful artifacts become the normal Lake
cache for subsequent work. A successful theorem proof establishes its
stated specification; it does not establish an unstated algorithm property
or discharge the hypotheses for a particular physical vehicle.
The [verification records](../docs/verification/README.md) preserve dated
results and the source hashes to which each claim applies.
Use `python scripts/verify.py --check-report PATH` inside the pinned shell to
check a saved record against the complete current source set. New unimported
files also invalidate an older record. The report records Lean's actual
loaded modules and counts the reused and recompiled module outputs, rather
than relying only on a textual import scan.

| Directory | Scope |
| --- | --- |
| Algebra | Block powers and nilpotent summation |
| Analysis | Continuous linear ODEs, differential-defect error bounds, comparison, analytic coefficients and mixed flows |
| Lie | SO(3), SE₂(3), manifolds, tangent algebras, actual exponential/logarithm and Jacobians |
| Dynamics | Gravity fields, exact mixed/log error dynamics, group-affine rigidity and representation criteria |
| Estimation | Group-affine errors, equivariance tests, bearing output bounds, noise coordinates and regional convergence certificates |
| Preintegration | Closed-form block exponential and mixed IVP |
| Magnus | Noncommutative coefficients, input algebra and flow composition |
| Planning | Dubins arc/line propagation, transverse Hermite offsets, metric correction, regularity, constant-speed reference derivatives and bank rate |
| [Applications](Applications/README.md) | Paper models, counterexamples and concrete flight/orbit certificates |
| Control | Lyapunov bounds, LMI certificates, polytopic tubes, contraction, port balances, flat-output and actuator backstepping, directional uncertainty and fuel certificates with data-error allowances |

Module paths reflect these areas. Declaration namespaces retain the existing
mathematical grouping under GNC; paths are not a second copy
of the declaration hierarchy.

For a concrete claim about an algorithm or physical system, identify the
theorem and discharge its hypotheses. Examples of the proved contracts are:

| Result | Proved specification and boundary |
| --- | --- |
| [Septic Hermite solver](Planning/Hermite.lean) | The returned polynomial satisfies all eight endpoint constraints and is unique among eight-coefficient polynomials, for arbitrary endpoint data and nonzero interval length. Exact rational computation agrees with real evaluation and derivatives. Full Dubins path selection is a separate obligation. |
| [Coast interpolation](Planning/CoastInterpolation.lean), [rotation kinematics](Lie/RotationKinematics.lean) | Twice continuously differentiable coordinate interpolation holds the prescribed burn values; rotation products and physical time scaling retain actual body angular velocity and acceleration, including the moving-frame cross term. Actuator feasibility and tracking require separate physical bounds. |
| [Rotation time change](Lie/RotationTimeChange.lean), [coast interpolation bounds](Planning/CoastInterpolationBounds.lean) | Reparameterizing a rotation path retains the clock-acceleration term in its actual angular derivatives. Monotone interpolation keys stay within their range; both derivatives vanish on every closed hold. |
| [Inertial burn injection](Dynamics/PlanarInertialBurn.lean) | A fixed inertial input cancels the intermediate RTN rotation exactly. Its in-plane pullback observables are signed fundamental-matrix entries under the existing symplectic inverse formula; gravity remains time varying. |
| [Orbital prediction certificate](Dynamics/OrbitalCertificate.lean), [polynomial supersolution](Analysis/PolynomialSupersolution.lean) | A complete differential defect, gravity-region check and scalar supersolution give uniform physical position and velocity prediction bounds. The region closes by a first-exit argument without an iterative tube assumption. Each application must check the defect and region conditions. |
| [Pointing-cap degree threshold](Applications/OrbitalComparison/PointingCapQuartic.lean), [physical obstruction](Applications/OrbitalComparison/PointingCapObstruction.lean) | For the specified 1200 s burn with two uncertain transverse pointing components, degree four is necessary and sufficient for uniform 1 cm position prediction within the transverse-polynomial class. An exact-component quadratic response has a checked bound below 3.120 mm. The proof includes complete inverse-square gravity and physical existence; it is not a minimum-FLOP theorem or a result for arbitrary pointing histories. |
| [Reachable-image certificate](Applications/OrbitalComparison/PointingCapReachable.lean) | Physical existence and uniform prediction error give two-sided set enclosures and a Hausdorff bound without convexification. Strict clearance of the predicted image implies physical avoidance. Numerical clearance and boundary extraction remain separate obligations; a pointwise approximation lower bound does not imply a reachable-set distance lower bound. |
| [Optimized coefficient records](Applications/OrbitalComparison/HornerGraph.lean) | Reassociated exact-component and quartic coefficients have fresh complete physical certificates. Their approximation classes and Hausdorff upper bounds are checked. The external graph optimizer and FLOP counts are outside the mathematical proof. |
| [Terminal cap support](Applications/OrbitalComparison/PointingCapSupportBounds.lean) | Two independent weighted-square certificates enclose the same worst terminal RTN displacement, with outward interval widths 6.240 mm and 8.433 mm. Both prove avoidance of a synthetic 850 m halfspace. Complete physical prediction errors and feasible pointing witnesses are included; these are terminal, constant-pointing results, not whole-flight obstacle certificates. |
| [Mixed log-linear lift](Dynamics/MixedLogLinear.lean) | Continuous time-varying mixed dynamics have an exact linear exponential lift for an initially exponential error. Agreement with a selected logarithm requires its chart conditions. This is not a classification of every group-affine field. |
| [Mission reference tube](Control/ReferenceTube.lean) | A regional differential supply, strict reserve and static tube inclusions prevent escape for the specified existing trajectories. Instantiating these conditions for the disturbed aircraft remains open. |
| [Independent-burn feasibility](Control/IndependentBias.lean) | Squared support certificates and nonnegative burn magnitudes imply feasibility for every admissible independent pointing direction; explicit row charges account for terminal-data errors. A concrete mission still needs its certificate values and physical-model correspondence. |
| [Constant burn](Control/ConstantBurn.lean) | Constant acceleration minimizes accumulated acceleration for a specified propulsive velocity integral. A centered first-moment condition characterizes when it also preserves double-integrator position. Orbital gravity and other mission constraints require their own validation. |
| [Reaction wheels](Dynamics/ReactionWheels.lean), [backstepping allocation](Control/ReactionWheelAllocation.lean) | Actual momentum derivatives give Euler balance, motor allocation, relative rotor speed and bounds including external torque for the stated ideal wheel model. Saturation, robust tracking and physical hardware qualification require further assumptions and proofs. |

These examples explain the scope of particular statements; the release audit
covers every GNC source module and declaration, not just this selection.

The general finite-column exponential is checked. The full manifold and
tangent construction currently specializes to SE₂(3), so the library does
not yet provide every SEₙ(3) Lie-group instance.
The reduced two-frame construction reuses mathlib's semidirect product.
It supplies exact discrete group-affine dynamics with linear actions including
scale. The similarity exponential is checked for any finite number of
translation columns; a complete similarity-group manifold instance is open.

Paper-specific flight/orbit models and counterexamples live in
[Applications/](Applications/README.md). Manuscripts, reviews and experiments
live in a separate papers repository that consumes this library as a
submodule. The import graph prevents general
mathematics from depending on an application.

[Verification/](Verification/Policy.lean) contains build/audit tooling under
the separate `Verification` module namespace. It is built by the default
Lake target and is part of the documented trust boundary, not a proof oracle.
[Tools/Planner.lean](Tools/Planner.lean) is the exact-rational planner interface;
its kernel functions have separate correctness theorems.

See [library design and upstream work](../docs/LIBRARY_DESIGN.md).
Application specialization and API refinement remain relevant before
submitting individual general results to mathlib.
