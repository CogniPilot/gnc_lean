# Current verification

**GNC is a formally verified mathematical library for guidance, navigation
and control.** Every included theorem is checked by Lean's kernel under its
stated hypotheses, with no admitted proofs or additional project axioms.

The [source-hashed record](latest.json) passed on
2026-09-16T08:58:13.247165+00:00. It covers:

- 1194 GNC modules: 1192 mathematical modules and two executable-tool modules.
- 32,568 theorem declarations among 39,407 declarations.
- 27,138 application theorem declarations, included in those totals.
- 73 passing library audit, release, cache and planner regression checks.
- 1,214 source/configuration files identified by SHA-256, including CI workflows.

All 1198 project Lean files live under `GNC/`; four are verification tooling.
Declaration counts include generated lemmas, not just statements in papers.
The only foundations are `propext`, `Classical.choice` and `Quot.sound`, using
released Lean 4.29.1 and mathlib v4.29.1. The audit separately recognizes 59
Lean-generated runtime companions.

This complete audit covers the library after separating it into its own
repository. All application proofs remain covered. Paper experiment programs
and their numerical comparison tests now belong to the consuming papers
repository, so their former counts are not part of the library regression
total or source-hash inventory. The final audit reused 1191 module artifacts
and rebuilt 3. The nonzero-initial uncertainty containment and existence
proofs, both concrete orbital records, covariance pushforward, coordinate
equivalence, positive semidefiniteness and deterministic-to-variance bound
are included. `PredictionMoments` additionally checks affine mean/covariance
propagation and every-entry covariance error bounds, including zero radii.
`InitialUncertaintyMoments` composes those bounds with both actual orbital
prediction certificates, all six physical outputs and Lie reconstruction
errors. Predictor moment bounds remain explicit hypotheses; no Gaussian or
independent-residual assumption is used. This is not a white-noise theorem.
The Monte Carlo runs and floating covariance calculations in
the consuming paper are empirical checks, outside this kernel claim. The released dependency cache setup
also passed from the standalone library directory.
The CI workflow is configured and syntax-checked locally; this record does
not claim a hosted GitHub Actions run.

`MovingTensorProjection` checks the actual derivative of a moving bilinear
tensor projection and its discarded mixed-component bound. Idempotence
suffices for the projected tensor to annihilate normal inputs. Taylor
weighting, full-basis cancellation and a conditional transition-kernel
error bound are included. The consuming paper's TDSTT2 adapter is numerical;
this generic theorem does not certify its physical trajectories or cost.
The module now also differentiates the synthesized low-rank query and bounds
its position/velocity kinematic discrepancy from moving normal directions.
`CartesianRadiusDefect` supplies a full-field Cartesian residual bound using
the same scalar inverse-radius constraint method as the Lie construction.
`TDSTTPolynomial` and four concrete `TDSTTData` records check the two rank-two
factorizations, exact initial values, candidate ranges and kinematic ranges.
`TDSTTData.Cartesian2.Prediction` now composes the complete physical
certificate for the fitted Cartesian rank-two query: 1.591368502 m and
0.066210187 m/s for every burn time and pointing vector in the declared
120 s / 0.1 rad family. It constructs the nonsingular physical solution,
identifies exact nominal initial data, and charges the delivered velocity's
kinematic discrepancy. `SmallOffsetDefect` bounds higher gravity and scalar
constraint products with explicit fourth-, sixth- and eighth-power growth;
`QuadraticTimeProfile` and `ExactDegreeProduct` justify the time growth and
finite coefficient assembly. All 32 generated checking files reproduce in
the consuming paper's pinned Nix target. `LieRadiusQuadratic` additionally
proves a lower-degree radius check and its growth bound; `TDSTTData.Lie2`
now completes the physical composition at 0.000992348 m / 0.000041743 m/s.
`TDSTTComparison` places both certificates on the same physical motions.
`TDSTTWitness` proves Cartesian actual error above 25 cm at the explicit
pointing vector (0.06,0.08,0) rad, while Lie is below 1 mm on the whole ball,
and an actual-error ratio above 250 at that witness. This uses exact rational
query evaluation and a proved Jacobian remainder, not numerical integration.
The claim concerns these concrete fitted rank-two predictors, not arbitrary
Cartesian algorithms or their higher-order/refined variants. These results do not verify the
raw numerical interpolant, coefficient generator or floating evaluation.

`TDSTTQuadraticObstruction` strengthens the fixed-candidate comparison to
the entire class of quadratic Cartesian position maps in the rotation vector.
Four admitted collinear inputs cancel every quadratic and leave a physical
endpoint-error lower bound above 2.4 mm, after charging the Lie certificate
and reconstruction remainder. Physical existence is proved at all witnesses.
`PolynomialLine` derives line evaluation and degree inheritance from mathlib,
so the obstruction covers every rank and every fitted coefficient choice.
A one-millimetre Cartesian polynomial guarantee requires degree at least three.
The consuming paper's cubic/quartic refinement experiment is numerical, not
a physical certificate or complete-cost proof.

`QuadraticResponseCertificate` checks the complete computed first-plus-quadratic
response defect, including both response residuals and the Hessian mismatch,
and its composition with a nonzero-initial physical polynomial envelope.
`QuadraticMajorant` checks a non-iterative response-size comparison with
an explicit gain domain; the response acceleration bounds include computed
defects. The concrete modules below instantiate these generic results to complete
the centered Cartesian physical certificate.

`CartesianResponsePolynomial` checks the executable polynomial surrogate
operators, coefficient-curve derivatives, uniform residual bounds, and
finite-feature combinations. `CenteredResponseData` checks eight linear
and 36 quadratic stored response residuals, their exact initial data, and
weighted all-time bounds for the whole declared feature box. A separate
pinned Nix target reproduced all 48 generated Lean files.
`GravityUnitReferenceApproximation` checks the gradient and half-Hessian
transfer without assuming the polynomial reference is unit length.
`CenteredResponseReference` checks the actual sharper oscillator residual
and its transfer to the physical nominal and varying-rate force.
`CenteredResponseAssembly` and `CenteredResponseDefect` check the complete
first/quadratic feature sums, their derivatives and assembled residuals.
`CenteredResponsePhysicalOperators` checks both physical operator budgets.
`CenteredResponseGeometry` discharges the rotation-induced forcing mismatch;
`CenteredResponseInitial` identifies the exact midpoint initial states and
proves their quadratic-in-angle norm bounds. `CenteredResponseBounds`
checks the computed response sizes. `CenteredResponseKinematics` derives
the actual candidate derivatives and full gravity defect; `RotationIsometry`
transfers them through the exact half rotation. The actual envelope records
check positive radius, physical gain, closure and outward display bounds.
`CenteredResponsePrediction.physical_prediction` now proves nonsingular
physical existence and 0.728244 mm / 0.012172 mm/s error bounds throughout
the 120 s burn, for every attitude in the three-axis 0.1 rad ball and every
physical motion with the prescribed midpoint initial state.
`CenteredResponseComparison.matched_physical_certificates` explicitly
places both completed certificates on the same physical motions.
Its budget-order theorem compares the certified bounds, not actual errors.
The consuming paper's prepared-query operation counts remain measurements,
not kernel theorems or full construction/certification costs.

`RotationCenteredError` checks the exact half-rotation midpoint compression,
the centered thrust identity and a quadratic angular displacement bound.
With an explicit positive radius floor, the initial inverse-square gravity
Taylor remainder is bounded by a fourth-order angular expression. These
pointwise results apply equally to Lie and Cartesian response methods.
They do not certify the consuming paper's new sampled three-axis screen or
its prepared-query expression counts.

`LieRadiusCertificate` proves the exact scalar Gram identity, an explicit
quadratic-inverse Jacobian residual including trigonometric tails, and a
full-gravity defect bound using a scalar inverse-radius constraint.
`LieRadiusFrame` connects this defect to actual inertial position and velocity
derivatives, with Coriolis, Euler and centripetal terms retained.
`LieRadiusApproximation` charges approximate-axis errors, inverse-cube
omitted products and sine/cosine tails; its squared-radius bound retains
quadratic and quartic time growth. `LieRadiusDefect` assembles a complete
pointwise full-gravity budget and derives the candidate radius floor and
nonnegative inverse-radius branch from its explicit candidate bounds.
`LieRadiusModel` identifies the executable polynomial residual, actual
candidate derivatives and normalized squared-radius error of the exact
inertial candidate. These are generic checked results.

`CoefficientNormProfile` proves coefficientwise Euclidean polynomial range
bounds without full polynomial squaring. It applies to Cartesian and Lie
representations alike. Six separately cached `LieRadiusData` input/range
modules check the delivered Lie coefficients, five direct polynomial
decompositions and their rational norm profiles. The aggregate derives
uniform parameter bounds and three quadratic-growth bounds. The concrete
phase and pointwise-budget composition is checked in `LieRadiusData.Bounds`;
`LieRadiusData.Envelope` checks outward rounding, the supersolution and coarse
closure. `LieRadiusPrediction.physical_prediction` proves existence and
0.626 mm / 0.0212 mm/s error bounds for every specified motion, throughout
the 120-second burn and for every allowed pointing angle. It uses the direct
Lie/scalar residual instead of constructing a Cartesian trajectory witness.
The earlier witness-based figures below remain valid. Numerical constructor
operation counts belong to the consuming paper, not to this library's kernel
theorem claim. The consuming paper's three-axis screen is not yet certified
by this one-angle result.

`BallMonomial` and `BallNormProfile` certify coefficient ranges over a full
three-axis Euclidean attitude ball. `JacobianPolynomial` checks its explicit
trigonometric tail and exact scalar Gram identity. `LieRadiusSpatialApproximation`
charges the reference and reconstruction errors in the candidate radius;
`LieRadiusFullDefect` retains the complete cubic inverse-radius factor and
scalar constraint. These generic results are included in the audit. They
do not certify the paper's new three-axis numerical coefficient proposal.
`TruncatedProduct` checks bounding discarded homogeneous products before
expanding them, and propagating existing factor errors including their product.
`BallPolynomialEnclosure` connects these rules to executable block arithmetic,
checked stored outputs, upward tail profiles and Euclidean vector bounds.
Its scalar coefficient-norm theorem avoids repeated rational squaring checks.
`DegreeProductCertificate` reassembles separately checked homogeneous
output pieces, avoiding one monolithic retained-product calculation.
These rules are shared by both coordinate systems.
`LieRadiusCubicEnclosure` transfers a scalar cubic-factor enclosure to the
full physical defect, charging both gravity terms with the joint multiplier
while retaining the separate radius constraint. It also proves the midpoint
skew cancellation and the contractive quadratic-skew bound.
The generated `JointErrorData` modules now check the actual three-axis
candidate, initial identities, full-ball ranges and complete Lie residual.
Degreewise affine product identities retain cancellation before bounding;
vector coefficient ranges and every discarded product are checked. The
entire cubic-factor tail is charged once with the Euclidean joint multiplier.
`JointErrorPolynomial` proves the executable model's semantics and physical
defect connection; `JointResidualCertificate` composes the numeric records.
`JointErrorReference` reuses the checked oscillator certificate after matching
the actual coefficient lists. It proves the exact unit-radius nominal,
position and velocity differential equations in full gravity, and spatial
reference/force error bounds including angular acceleration.
`SumProductCertificate` checks cancellation-preserving sums of homogeneous
products. `JointRadiusCertificate` derives the exact scalar Gram factorization;
the concrete `JointErrorData.Radius` and `Constraint` modules check every
retained coefficient, ball range, radius tail and inverse-radius constraint.
`JointErrorKinematics` proves the exact reconstruction derivatives.
`JointErrorData.Ranges` derives uniform candidate bounds from checked profiles.
`JointErrorPhysicalDefect` combines all concrete records into the full nonlinear
gravity/thrust defect on the complete attitude ball and burn interval.
`JointErrorData.Budget` bounds the actual normalized physical defect with a
rational time profile. `JointErrorData.Envelope` checks outward rounding,
the supersolution, positive-radius closure and SI display bounds.
`CandidateOrbitExistence` supplies a reusable physical existence theorem
from a candidate and its defect. `JointErrorInitialState` identifies the
stored initial data with the physical midpoint family, including zero rotation.
`JointErrorPrediction.physical_prediction` completes the all-time,
whole-ball trajectory certificate: 2.916033 mm and 0.052027779 mm/s over
120 seconds for the stated midpoint family with rotation norm at most
0.1 rad. `motion_initial_midpoint` connects its physical motions to that
family. The matched Cartesian certificate remains a separate paper obligation.

New large residual records use Lean's exact `mkRat` constructor to avoid slow
elaboration of overloaded divisions. Kernel arithmetic checks are unchanged.
Lake allocates 64 MiB of thread stack for the largest norm-profile records;
the resource flag preserves proof-content cache keys. These are verification
engineering changes, not additional axioms or a certified runtime speedup.

`StateTransitionTensor` and `MixedStateTransitionTensor` check the exact
linear transition, vanishing of every higher initial-error derivative,
reconstruction of actual matched mixed-invariant trajectories, and restriction
to the Lie algebra under the stated geometric hypotheses. A smooth residual
supplies all higher vector-field derivatives. Physical reconstruction needs
a valid Lipschitz bound and region membership. The reconstruction tensor
identity and a nonzero directional witness are checked using mathlib's
higher chain rule. These use initial algebra-error parameters and do not
imply that every Cartesian state transition has nonzero higher derivatives.

The short-burn orbital Lie-STT pipeline now has a complete physical
certificate with exact factored output. `LieErrorReconstruction` proves that
the actual SE2(3) exponential cannot enlarge a translation radius at shared
attitude. `LieSTTOutput` transfers the offline polynomial surrogate to the
factored query, charging every removed coefficient and phase/trigonometric
tail; `LieSTTData.Output.prediction` proves the concrete 0.000670087 m /
0.000022614218 m/s bounds over the complete 120 s family. Four common
polynomial time-profile records and the stronger exact-direction Cartesian
comparators are checked and exported. The latter win this short-burn test.
The original long-burn angle-jet screen remains numerical diagnostics.
The Nix benchmark reproduces all records, optimized FLOPs and separate
rational-proposer work. These counts do not verify compiler cost or final
binary64 query evaluation. The direct one-angle constructor described above now avoids that witness;
the all-axis concrete certificate is also complete; the matched complete-cost
comparison remains unfinished.

`LieGravityPullback` checks the exact finite-angle thrust identity, the radial
gravity reduction and its derivation from actual physical position/velocity
equations. It includes zero attitude and requires a fixed inertial offset;
the physical gravity field remains state dependent.
`SpinningOrbitRefinement` checks a constructive comparator: 32 local quartic
rate responses certify normal-velocity error below 0.01 mm/s throughout the
physical burn, using one shared source profile and nonlinear gravity budget.
The coefficient responses are mathematical ODE solutions, not certified
floating-point tables. The supporting `QuarticHarmonicResponse` and
`MonomialSecondOrderBound` proofs account for the actual source tail.

`SpinningOrbit` now checks physical existence, 100 m coarse closure and the
nonlinear-gravity remainder for the uncertain-spin family. The spatial
retained-gradient response certifies below 5 mm / 0.011 mm/s throughout the
burn. `SpinningOrbitNormal` checks its explicit oscillator, a physical error
below 0.0082 mm/s, and the universal quartic obstruction above 0.97 mm/s with
an actual factor-118 witness. `SpinningThrust` and `UncertainSpin` supply the
underlying thrust-response witness. A classical modal construction ties;
the numerical evaluator and CPU performance are not verified.

`MixedSphereResponse` proves a seven-feature correction with only a
cap-depth-square omitted quadratic source. `PointingCapCorrectedComparison`
checks the complete physical 1.340259 mm / 0.009834489 mm/s certificate,
actual query reconstruction and 19 operations, versus the full component
record's 2.016270 mm and 23 operations. Four stronger cumulative-coefficient
profiles have independent Lean checks. `GravityTimeProfile` and
`MonomialSupersolutionComparison` prove the conditional sixth-order gravity
source and its 28-fold improvement over charging the same source constantly;
this additional gravity refinement is not used in those numerical records.
`UncertaintyTruncation` proves the exact cubic-ODE regression oracle used
to test external Taylor-model truncation; the external solver is not verified.

`ReducedSphereResponse` checks the original direct five-feature construction:
five time-varying response equations, zero initial conditions, exact omitted
Hessian terms and their cubic/quartic cap bounds. It also checks the
13-operation spatially factored query algorithm. The direct construction now
has its own complete physical certificate: 8.914232 mm position and
0.053744171 mm/s velocity error over the whole 1200 s pointing cap and burn.
`PointingCapTimeCertificate` applies a common polynomial-in-time residual
checker to direct, full-component and transverse-quartic candidates, including
full inverse-square gravity and first-exit region closure. The comparators
certify 2.016289 / 2.968219 mm; all meet 1 cm and 0.1 mm/s.
`PointingCapDirectComparison` binds the actual queries to these physical
records and checks 13 / 23 / 25 scalar operations with prepared coefficients.
`MonomialSupersolution` derives the explicit noniterative envelope from actual
polynomial derivatives. Six generated data/profile modules are independently
checked by the kernel. Generation graphs and rational proposer counts are
reproducible experiments, not a verified compiler or end-to-end cost theorem.

`SphereRankOne` proves exact sphere reduction before compression and the
planar/normal error composition. `PointingCapGeometryCompression` checks a
four-feature predictor with complete physical position error at most
9.323809 mm over the stated 1200 s burn and pointing cap. `PointingQuery`
and `PointingCapQueryComparison` bind counted arithmetic to the actual
certified coefficient records: 11 operations for the compressed predictor,
25 for a factored quartic with a 4.045377 mm bound. The quartic also uses
the supplied radial component; it needs 26 operations with only transverse
inputs. Both satisfy one centimetre, with different bounds. These are
real-arithmetic query counts with prepared coefficients/direction inputs;
offline construction/certification and floating-point execution are separate.

`RankOneCurvature` checks a four-point, unit-variation witness on the line
perpendicular to a rank-one quadratic direction. `PointingCapRankOne` checks
exact endpoint coefficient extraction and composes the witness with the
previous physical orbit certificate. Every degree-four transverse endpoint
expansion of the stated rank-one directional form has actual position error
above 8.36 m somewhere in the specified 1200 s cap. Its coefficients and
higher-order directions are arbitrary. Physical existence, admissibility and
the full-gravity error budget are included. Full-rank quartics, nonlinear
input charts, higher degree and subdivided compositions remain outside the
obstruction. The separate published-compression script is an untrusted
diagnostic; this universal class theorem does not depend on its optimizer.
The incremental audit reused 890 module artifacts and rebuilt 2; released
dependency caches were reused.

`RotatingForce` checks the exact harmonic reduction of a fixed ambient map
through a planar reference rotation. `RotationPhaseCertificate` proves a
`C*t` phase-residual bound and its vector forcing estimate without charging
the known angular rate as exponential growth. `VaryingRateReference` checks
a physical powered circle with changing speed, its angular-rate kinematics,
required radial/tangential thrust and exact oblique pointing source. The
Python screen is an untrusted numerical proposal. Two selected inertial-offset
records now have separate complete physical certificates; the other screen
rows remain uncertified.

`VaryingRateFrame` now checks the full moving-frame reconstruction, including
angular acceleration, and its inverse-square candidate-defect bound.
`PolynomialPhaseCertificate` and `VaryingRatePhaseData` check both rational
reference harmonics of the new 1200 s experiment. `QuarticPointing` proves the
degree-four angle source's Taylor remainder. `VaryingRateForcing` connects
the source to an actual oblique rotation and bounds its phase/angle defect.
`VaryingRateBurn` and `VaryingRateCertificate` supply physical existence,
the full residual and first-exit region closure. No bound on an unknown
physical orbit is assumed in the resulting trajectory certificate.

`VaryingRateData.Retained` and `Quartic` check the exact rational records for
the stated 1200 s varying-rate burn and every angle in ±0.1 rad, with uniform
position bounds below 0.164 and 1.461 mm. `Comparison.actual_error_strict`
proves that the supplied quartic's actual endpoint error exceeds twice the
retained error at θ=0.1, including trigonometric evaluation error in the
separation witness. It does not rank all quartic STT methods. The exporter
reproduces the numerical records exactly. Coefficient generation and FLOP
counts remain untrusted experimental code, independently checked through
the supplied predictor's complete physical residual.

`SpacecraftGroupAffinity` checks the exact group-affinity defect of the
spacecraft matrix field. Prescribed acceleration and angular-rate terms
cancel; a linear gravity field leaves a rotation commutator. The isotropic
affine case has checked state-independent mixed coefficients even when its
inputs vary with time. `MatchedAttitude` proves preservation of a constant
inertial attitude offset for actual solutions with arbitrary matched
continuous body rates, including changing axes. Its unmatched-rate derivative
and roll-transfer identities delimit the uncertainty model. The generic
`FiniteAngleComparison.certified_separation` turns a supplied complete
physical error bound and predictor separation into an actual accuracy
comparison. These results add no arbitrary-history numerical certificate,
nominal Magnus termination or state-of-the-art performance theorem.

The nonlinear extension proves a local convergent Lie series for polynomial
ODEs and connects it to the spatial orbit's exact inverse-square lift.
`PolynomialLieSeries` checks the executable differential recurrence at every
order. `PolynomialLieConvergence` derives factorial coefficient bounds and
the actual Taylor remainder, then proves convergence when `C * d * T < 1`.
Here `C` bounds component coefficient sums and `d` bounds their degrees.
The theorem assumes a smooth solution on an open interval and a proved unit
box enclosure on the step. It does not assume analyticity or convergence,
but does not discharge those solution and enclosure hypotheses itself.
`ExactLieSeries.physical_lift_series` retains those hypotheses and the
positive-radius condition for the prescribed spatial orbit model. Arbitrary
input histories, an optimized evaluator and global continuation remain
separate obligations.

`Magnus.StateDependent` checks the additional coefficient-derivative terms
in nonlinear vector-field brackets and the exact local SE2(3) logarithm ODE.
`Magnus.NonlinearGravity` proves the actual first brackets and all-order
nonzero radial derivatives. `Magnus.GravityFactor` proves termination after
the second gravity-side Magnus term and the resulting factor's ODE; its
gravity moments still depend on the unknown physical trajectory.
`Magnus.InputTerms` checks zero-rotation and common-axis bracket
cancellations. `GravityReferenceDefect` and `GravitySecant` distinguish known
reference histories from the exact displaced gravitational field.
`NonlinearInteraction` checks removal and reconstruction of a nonlinear drift
under explicit flow-differential hypotheses; it does not construct the
Kepler or Stark flow. None of these results is a finite closed form for
arbitrary spacecraft motion or a performance-superiority theorem.

`Magnus.ClosedExponential` connects the existing mixed-invariant coefficient
formula to the actual time-extended 5×5 matrix. It checks its five-power
relation, exponential, zero-rotation case, Lie subalgebra, closure under
nested commutators and coordinate integration, and the left Gauss-Magnus
coordinate identity. This is the established special Galilean algebra;
the exponential is also present in related Galilean preintegration
literature. The October 2023 SINS precursor explicitly uses the nilpotent
block and predates the December 2023/November 2024 arXiv postings of Kelly
and Delama et al. This chronology is separate from Lean verification.
The result does not sum the unknown Magnus coordinates, prove
Magnus convergence, or solve state-dependent orbital gravity. Its 96
binary64 comparisons are diagnostic and do not certify rounding.

`ForcedProductConvolution` proves the scalar product-forcing response at
zero and resonant rates. `ForcedProductResponse` assembles the actual
quadratic modal ODE, its zero initial data and an evaluation-error bound
with explicit kernel-error hypotheses. `QuadraticModalCancellation`
proves exact removal of the first two response polynomials, and a third
for the position projection under acceleration forcing. These algebraic
cancellations can improve evaluation; a certified scalar implementation
and matched optimized cost comparison remain separate work. Cartesian
implementations share the same cancellation identities.

The new rotating gravity transition uses mathlib's Cayley–Hamilton theorem
and proves equality of an elementary four-matrix expression with the actual
exponential. Scalar derivatives, constant forcing, the normal block, orbital
roots, physical block decomposition and the HCW limit are included.
`FiniteBurnTargeting` checks the burn/coast/burn endpoint composition.

`ExponentialConvolution` proves the elementary forced-mode formula, its
derivative and zero initial value, including exact resonance.
`ModalQuadraticResponse` composes those modes into the second gravity-response
ODE. `BiquadraticSpectrum` and `RotatingGravitySpectrum` discharge the spectral
identities for the actual powered-circle generator under `k > 0` and
`w² < k`. The result evaluates the retained response hierarchy without a
time-series truncation; it does not eliminate the higher-order physical
gravity remainder. The binary64 evaluator and its 20 numerical comparisons
are diagnostic tooling, not a certified evaluator or performance theorem.

`CentralGravityAlgebra` checks the exact canonical full-gravity change of
variables, the three-generator matrix commutator algebra, its mathlib
`IsSl2Triple`, the quadratic power identity and equality with the actual
matrix exponential. It also checks the extra derivative of the
state-dependent gravity coefficient. Matrix closure along a trajectory does
not determine its unknown radius history, establish nonlinear vector-field
closure, or prove Magnus convergence. `RotatingKeplerRegularization` checks
the planar canonical one-form and complete regularized energy, including
the mixed term obstructing a specific additive Stark separation. Complete
regularized-flow equivalence and physical-time inversion remain unproved.

The full nonlinear search adds exact radial-thrust energy and momentum
identities, a cubic reduction, and an identity for mathlib's Weierstrass
function under explicit lattice-invariant hypotheses. The rotating-thrust
Jacobi energy is also checked. These statements do not complete a nonlinear
orbital initial-value propagator: lattice/phase construction, real branches,
angle reconstruction and physical-time inversion remain separate obligations.

The 54-direction support sweep proves physical support intervals and common
arrival-set enclosures for retained pointing and a quartic, including the
interior support case. Its two generated records match the pinned producer.
Support widths do not bound polytope faceting error; floating-point proposals,
operation counts and projected-vertex calculations remain outside the proof.

The force-component STT extension checks the first/second Cartesian response
ODE, zero initial data, and equality with the retained-angle quadratic class
after exact circle reduction. Four new coefficient records plus four
analytic-nominal adapters certify the complete inverse-square physical
prediction bounds. The matched second response uses 481 versus 541 measured
generation FLOPs, with the same displayed error limits and rational
multiplication count. The physical bounds are kernel checked; the generator,
C compiler and operation counts remain outside that proof. Nix reproduces
all eight coefficient/adapter files byte for byte.

The final incremental verification reused 811 modules from Lake's checked
build cache and rebuilt three modules. Eleven disk norm records and
their coefficient records match the pinned producers byte for byte; six are
selected by the current search. The two new coefficient records use a quartic
anchored Chebyshev source and quintic response at time degrees 13 and 14.
Their separate builds and all norm checks passed and are cached.
`PointingCapDiskComparison` checks the response degrees, requested physical
limits and both half-millimetre predictions around a single existing
trajectory. The 396-case optimizer, 57,024 graph schedules
and operation counts remain numerical tooling, outside the mathematical
proof boundary. Selection by compiled arithmetic chooses the same cases.

`DiskMonomial` proves disk monomial bounds using mathlib's weighted AM–GM
theorem, orthogonal-column bounds and a Bernstein squared-norm interface.
`PointingCapRefinement` transfers arbitrary proved norm estimates to the
complete physical certificate and permits componentwise minima of sound
estimates. The required `Bounds.Sound` hypotheses are explicit.
`HomogeneousPolynomial` proves the Pascal-based positivity checker;
`DiskPolynomial` checks each actual vector decomposition and squared-norm
bound. `PointingCapDisk` and eleven concrete records now discharge the full
physical obligations. Both representations use these refined bounds in the
published frontier. Exact time degree 12 tightens to 2.933826 mm; the selected
half-millimetre pair gives 0.290900 / 0.328373 mm with unchanged coefficients.
Generation costs are 520 / 571 FLOPs at 1 mm and 520 / 700 at 0.5 mm.
These are measured comparisons with the tested polynomial families, not
state-of-the-art superiority or mathematical complexity theorems.
`DirectionalTensor` reproduces
the rank-one projection identity, global Frobenius-optimality characterization
and contraction bound, and composes tensor-compression errors with a separate
physical-flow remainder. Its line-restriction and degree theorems are connected
to the actual orbit obstruction by `DirectionalObstruction.physical_comparison`.
This covers fixed-degree directional expansions on the benchmark's linear
angle input; it does not verify an eigensolver, nonlinear input charts or
computational superiority of a complete external pipeline.
The new `SphereResponse` module
proves a quadratic response reduction for arbitrary unit thrust directions,
its SO(3) specialization, a rational forward-cap bound and the time-dependent
response ODE. Its earlier 624-case numerical screen remains exploratory.
The separate `PointingCapCertificate` chain now constructs unique physical
solutions and checks complete inverse-square prediction errors for all 14
selected two-direction records, at 600 and 1200 s. The retained, component,
balanced, Taylor and Chebyshev records match the pinned Nix outputs byte for
byte. The larger proposal grids, floating-point generators and operation
counts remain numerical tooling.

`PointingCapObstruction` proves that every transverse cubic exceeds 11.7 mm
of physical endpoint error somewhere on the 1200 s cap, while the exact
direction-component response is certified below 3.120 mm throughout the
burn and cap. The lower bound is the exact signed-witness signal minus the
derived physical error; its numerical display is checked rounding.
`PointingCapQuartic` proves the stored quartic's actual polynomial degree,
evaluation and uniform physical accuracy below 4.217 mm. Degree four is
therefore necessary and sufficient for the declared 1 cm requirement in
this polynomial class. `PointingCapChart` proves equivalence with the
square-root parametrization, and `cap_prediction` includes physical
existence for every transverse pair in the disk. These are not minimum-FLOP
or arbitrary-pointing-history theorems. Component STTs inherit the exact
geometry. Their original recurrence is cheaper; matched algebraic graph
optimization now gives both constructions the same 344-FLOP kernel.

The new `HornerTime12Burn1200` and `HornerTaylor4Time12Burn1200` records
independently certify the reassociated coefficients against the complete
physical ODE. Both match the pinned graph-audit Nix output byte for byte.
`HornerGraph` verifies their approximation classes and extends the shared
physical-family Hausdorff bounds. The new physical limits have the same
outward displays as their predecessors. The measured generation counts are
344 versus 447 FLOPs after matched optimization; neither the optimizer,
native compiler nor these operation counts is formally verified. The
144-schedule search is not a proof of minimum arithmetic complexity.

`ParameterPolynomialCertificate` checks time specialization and weighted
squares. `PointingCapSupport` proves soundness of a rational polynomial
support certificate using nonnegative weights, the exact sphere identity,
a proved cap-depth inequality and a weighted-square disk multiplier.
`PointingCapClearance` connects these identities to physical terminal support.
The two `PointingCapSupportData` records and `PointingCapSupportBounds`
check support intervals for the same physical family along RTN normal
(0,3/5,4/5): [847.145577,847.151817] m and [847.144156,847.152589] m.
Both prove a synthetic 850 m terminal halfspace clearance. Witness feasibility,
physical errors and outward display rounding are checked. This does not
certify avoidance at intermediate times or an operational rendezvous mission.

`PolynomialBallMap` proves the explicit cubic cube-to-ball map in dimensions
at most four, including surjectivity and the scaled disk specialization.
`BivariateBernstein` and `BernsteinRectangleTree` reuse mathlib's Bernstein
properties to check polynomial reconstruction and a complete rectangle
cover. `PointingCapPolynomialQuery` transfers a polynomial upper bound and
feasible witness to physical terminal support. `PointingCapBernsteinData`
checks all 28 numerical leaves and the interval [847.143928,847.153004] m,
of displayed width 9.076 mm, including the complete physical error and
outward rounding. The independent rational CORA-conversion implementation,
adaptive proposal generator and operation counts remain unverified tooling;
Nix reproduces the numerical certificate and report byte for byte. This
is not a MATLAB/CORA execution or full-pipeline performance certificate.

`CertifiedImage`, `PointingCapReachable` and `PointingCapSetBounds` now
connect the physical prediction certificates to reachable position sets.
They prove both directed error-ball inclusions and Hausdorff upper bounds
of 3.120 mm for each exact-component representation and 4.217 mm for the
quartic, against the same physical family throughout the 1200 s burn.
Strict clearance of the predicted image transfers to physical avoidance;
computing that clearance remains an explicit premise. A checked relabeling
counterexample shows why the pointwise cubic obstruction does not imply
a lower bound on set distance. These results cover the stated constant
pointing cap, not arbitrary control histories or a certified obstacle solver.

Supporting modules are checked and exported by `GNC.Core`:
`ParameterPolynomial` verifies sparse parameter/time arithmetic and uniform
Bernstein range bounds; `RadialSourceCertificate` bounds the forward-cap
source error from its unit-length polynomial residual; and
`ScaledForcedOrbitExistence` proves a rescaled-state existence condition for
a larger gravity gain. `BernsteinSubdivision` proves sound source-range
refinement; `ParameterPolynomialDegree` connects actual sparse records to
mathlib's multivariate polynomial degree. `ParameterPolynomialRange` proves
that reusing independently kernel-checked scalar ranges preserves the
original bound exactly, without changing coefficients or error budgets.
These general results are composed in the 14 physical cap certificates.
The low-order
approach-cost screen remains numerical tooling; it does not add Lean mission
certificates or change the existing physical arrival theorem.
The new `SylvesterResponse` module proves the response identity with flow
and Sylvester residuals charged, its classical inverse-frequency recurrence,
and the transformed dynamics for a time-varying change of variables.
`HarmonicPointing` proves uniform sine/cosine source bounds and the second
harmonic identity, including the mean thrust loss.
`HarmonicPolynomial` now checks derivatives, initial matching and coefficient
residual bounds uniformly over the unknown phase. `GravityRemainderMonotone`
proves monotonicity of the sharp gravity remainder with displacement radius.
`HarmonicBurn` constructs a unique nonsingular physical orbit at every
prescribed frequency and phase for the fixed amplitude `11/630` rad. These
supporting results now compose through `HarmonicFrame`, `HarmonicDefect`,
`HarmonicMode` and `HarmonicCertificate` into eight concrete physical
certificates in `HarmonicData`. Both frequency-aware solvers meet 1 cm /
0.1 mm/s prediction error throughout 600 s for every phase at four fixed
frequencies. They also check the outward-rounded physical position and
velocity dispersion bounds printed in the supplement. The complete 280-case
grid, generation FLOPs and native-output checks remain numerical tooling;
only the eight selected records are concrete Lean physical certificates.
The classical inverse-frequency series is cheaper at the three higher
tested frequencies. Neither a universal geometric speedup nor a combined
variable-mass/controller-realized oscillatory arrival theorem follows.
The multibody extension checks actual moving-center derivatives, summed
gravity remainders, and shared ephemeris-error cancellation with the reference
gradient retained. The public Orion reference importer separately passes
eight regression tests in its pinned Nix build; it is numerical tooling,
not a Lean-verified parser or a lunar-flight certificate.
It also checks the new finite-horizon disturbed attitude-controller bounds,
their log-error-to-physical-pointing connection, forced componentwise
certificates, variable-mass thrust identities and the illustrative Orion
scalar propulsion bounds. The controller-derived spherical-cap support and
synthetic Orion-scale arbitrary-history impulse bounds are also checked,
including the moving-reference-frame interpretation and a nonzero steady-bias
equilibrium. These are mathematical results under explicit
hypotheses, not an Orion flight-controller or arrival certification.

The Magnus derivation checks the first three displayed left-Magnus terms,
the full triangular block commutator, cross-time coupling cancellation,
the actual coupling exponential and the surviving gravity cubic coefficient.
The computed-adjoint extension proves the actual polynomial chain rule,
an explicit quadratic remainder majorant and endpoint pairing bounds with
the adjoint approximation error charged. Twelve exact-rational residual
records are checked for the zero-common-bias RTN motor example. Its full
scalar composition now connects directional input support, every numerical
handoff, terminal matching and the physical nominal's error. Terminal
along-track bounds are 695.64 m for the cylinder and 1655.61 m for the box,
relative to an actual undisturbed trajectory. Physical existence for every
admissible continuous cylinder input and the inertial projection are checked.
Nix reproduces all 25 adjoint/support/composition records byte for byte.
These input-set bounds do not establish a Lie-versus-Cartesian advantage.

`OrbitalSymmetry` checks full gravity/drag trajectory reuse under a constant
isometry, with a J2 correction when the rotation fixes its axis and commutes
with atmospheric spin. Existing nominal certificates transfer without norm
amplification. The initial state and thrust must transform together; the
theorem is not a thrust-only misalignment result. Known-target cancellation
and uncertain-ephemeris composition are also checked. The eight-case
application screen remains numerical: its solver samples, operation counts
and new nominal trajectories are not new Lean numerical certificates.

The refined finite-burn comparison checks two second-gravity-response
candidates against the full inverse-square ODE, including the reconstructed
phase, inverse-radius constraint and region closure. Their uniform relative
position bounds are 15.301 µm for retained finite angles and 58.612 µm for
STT7, over 600 s and the full ±0.35 rad interval about the specified spatial
axis. An additional full-recurrence STT7 comparator proves 96.984 µm.
The radial/transverse gradient and Hessian identities are also checked.
The larger refinement grids and operation counts remain numerical tooling;
they do not prove a complete certification-cost advantage. A separate
atmospheric-spin theorem bounds the acceleration defect when the selected
rotation ceases to be a symmetry. It has not yet been composed into a new
arrival certificate for the spinning-atmosphere screen.

The subsequent exact-frame checker proves the actual 3D moving-frame
derivatives, explicit Coriolis and centrifugal terms, and radius/defect norm
preservation. It composes the full inverse-radius and physical-ODE bounds
with first-exit closure. Four new `RotatingData` records certify the second
and full gravity response with finite angles or STT7. All meet the joint
100 µm / 1 µm/s requirement throughout the same 600 s spatial family.
The second finite-angle candidate proves 28.914 µm and 0.5242 µm/s.
Nix reproduces all four coefficient files byte for byte, the 220-case
proposal grid, the operation-count figure, and compiled C correspondence
checks. The operation counts and compiler execution are numerical tooling,
not Lean complexity theorems or an optimized Chebyshev/GIPA benchmark.

The stronger comparison adds a checked Bernstein bounder for the spatial
source and four `RotatingBernsteinData` records. Second/full gravity responses
with finite angles or degree-six Chebyshev-source polynomials all pass the
same physical checker. The new `SpatialExactNominal` module connects the
analytic powered circle to the physical ODE, proves uniqueness in the
candidate-derived region, and removes the extra nominal budget equally for
both representations. Four `ExactNominalData` adapters reuse the cached
coefficient proofs. The second finite-angle response certifies 13.396 µm
and 0.2434 µm/s; the matched Chebyshev-source response certifies 40.694 µm
and 0.3341 µm/s. Interpolation, conversion and source truncation errors are
charged against the independently proved physical source; NumPy is not
trusted. Nix reproduces all four coefficient files byte for byte, the
396-case proposal grid, four compiled-output checks and the main paper's
arithmetic figure. This implements GIPA's elementary-source construction
with a common inverse-radius lift and bounder; it does not verify SMART-UQ
or establish a universal efficiency comparison. Setup and cached certificate
arithmetic are disclosed separately from generation FLOPs.
The new Nix wrapper reproduces all four adapters byte for byte and measures
cached rational-certificate costs for all 122 passing proposals in the
396-case screen. The remaining proposals and operation counts are numerical
tooling, not additional Lean instantiations or complexity theorems.

The polynomial-class extension proves a lower bound for arbitrary real
degree-six endpoint polynomials. Eight rational nodes and signed weights
have zero moments through degree six and unit total variation. The complete
physical and trigonometric evaluation budgets leave a lower bound above
3.88 µm at some admitted pointing angle. A separately checked retained-angle
time-12/inverse-10 candidate has a uniform upper bound of 0.989067 µm.
`PolynomialObstruction` proves the general signed-witness argument;
`PolynomialObstructionData` and `SpatialPolynomialObstruction` connect the
numerical witness to physical orbit solutions. The new coefficient record
and nominal adapter are also checked. This is an approximation-class result,
not an execution-cost theorem or a bound on higher-degree, piecewise or
nonpolynomial methods. The Nix package reproduces all three generated Lean
files and the compiled output of the 541-FLOP candidate generator.

`SpatialExistence` now constructs the spatial benchmark's physical solution
for every real angle and all three prescribed thrust laws, with noncollision
and uniqueness throughout the 600 s burn. `EuclideanClip`,
`ForcedOrbitExistence` and `ForcedOrbitUniqueness` prove the reusable bounded
extension and first-exit arguments using released mathlib's ODE theorems.
Clipping is proved inactive on the constructed solution. The composed
`SpatialPolynomialObstruction.physical_comparison` therefore has no supplied
trajectory, existence, radius or noncollision assumption. Its coarse
existence enclosure is not added to either sharp prediction-error bound.

The refined matched comparison allows higher polynomial degrees at a common
1 µm / 1 µm/s requirement. Three additional polynomial coefficient records
and nominal adapters check the selected Chebyshev-7/8 and Taylor-STT8 physical
bounds. `RefinedAccuracy.minimum_degree` combines degree-seven sufficiency
with the existing degree-six obstruction: the minimum ordinary endpoint
polynomial degree is exactly seven, allowing arbitrary real coefficients.
`BivariateDegree` verifies coefficient-list degree and evaluation, while
`FiniteAngleSpan` and `SpatialFiniteAngleSpan` prove that the retained
predictor uses five fixed angular functions. These mathematical results
do not verify the expression-graph optimizer or prove a FLOP lower bound.
The source-hashed Nix experiment reports 541 / 2172 / 3864 generation FLOPs
and 24790 / 116019 / 153549 preparation/cached-certificate rational
multiplications at the same target, for retained angles / Chebyshev sources /
Taylor-STT. Different Chebyshev candidates attain its two minima. Setup,
preflight, cold matrix work, compiler execution and online queries remain
separate; the counts are not a universal algorithmic or CPU-speed theorem.

The new synthetic motor burn/coast application checks another 48 step
records and four complete compositions. The full inverse-square field
includes reciprocal mass and arbitrary bounded continuous acceleration
histories on each arc. First-exit containment bounds every specified
solution, while a separate construction proves existence for every
admissible continuous input. Mass and state pass exactly through all
handoffs; physical radius and mass stay positive. The mass-ratio bound
and inertial SI error norms are checked, including frame rotation.
The real mass-flow coefficient's rational approximation is explicitly
charged as initial error. The pinned generator reproduced all 52 new
Lean records byte for byte; the prior 52 approach records are unchanged.
Retained rotation and STT2 give nearly equal bounds under this broad
input box. This certifies the stated synthetic model, not the actual
Artemis trajectory, a realized spacecraft controller or a fuel advantage.
The new two-burn approach certificate includes all 48 segment records and
four composed mission proofs, for retained rotation and directional STT2
under both RTN-fixed and inertially fixed commands. For every pointing angle
in ±1° about the specified oblique axis, the proofs construct a nonsingular
physical solution through both burns and the coast, preserve the same angle
at handoffs, and establish the terminal position and inertial-velocity bounds.
The generic componentwise certificate, inverse-radius and phase constraints,
and SI reconstruction are checked. The pinned Nix generator reproduced all
52 generated Lean records byte for byte. These guarantees use the exact
initial state, prescribed commands and ideal inverse-square model; both
representations meet the specified 25 m / 0.05 m/s arrival requirement.

It includes the parameterized second-order residual comparison, its
first-exit region closure and the full inverse-square physical specialization,
with the auxiliary strict margin eliminated. The explicit free-gain polynomial
supersolution and retained-angle response derivative and initial data are
also checked. The main paper's exact coupling factor, shared nominal-gravity
cancellation and terminal error-budget composition use existing audited results.
This includes all 31 spatial finite-burn coefficient records, including the
additional seventh-order comparator, retained in Lake's cache. Exact rational terminal
queries prove six-component physical endpoint boxes and the illustrative
1000 m / 3.5 m/s screen for all three laws. The checked point evaluator also
proves a stored STT7 predictor's actual endpoint error exceeds 15 μm, while
the structured predictor stays below 0.5 μm over the entire RTN/RTN family.
This includes trigonometric evaluation and physical prediction errors.
The audit also includes the analytic Gauss/Magnus
remainder results, physical inverse-radius lift and shifted error equations,
and independent confirmation of the selected planar and spatial Flow* physical bounds.
The spatial extension proves all seven shifted derivative components and
confirms all 36 repeated relative-prediction reports against the full physical
model. Reported frontier bounds use the larger of the external report and
the independently proved bound; the one necessary weakening is disclosed.
The spatial certificates cover the disclosed fixed-axis families under both
RTN offset conventions and inertially fixed thrust. They charge the computed
physical nominal's error as well as the perturbed trajectory's error.

These proofs do not verify Flow*'s C++ execution, CPU measurements,
floating-point query evaluation, or the concrete 1200-second Kepler+M4
numerical STM. The selected Flow* physical bounds are independently established
using GNC's full-field certificates; this is not a proof of Flow*'s internal
certificate construction. Other application and physical-model boundaries
remain as stated in the [verification contract](../VERIFICATION.md).

Run `nix develop --command python scripts/verify.py` for an incremental build,
axiom audit and regression checks. Lake retains checked project artifacts in
`.lake/build` and released dependency artifacts in `.lake/packages`. Use
`--fresh` only when an explicit complete rebuild is needed; its successful
proof cache is also retained. Check correspondence with the current sources:

```sh
nix develop --command python scripts/verify.py --check-report docs/verification/latest.json
```

A verification record attests only to its exact source snapshot.
