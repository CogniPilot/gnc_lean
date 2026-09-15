# GNC library design

**GNC for Lean** is the Lake package `gnc`. All project `.lean` files live
under `GNC/`. General mathematics is exported by `GNC.Core`; every paper's
formalization is exported by `GNC.Applications`; `GNC.All` imports both. The planner CLI is in `GNC/Tools/`; it is built and audited
without introducing its `main` into the public mathematics import. The default `Verification` target builds and audits the
complete development. Verification tooling uses its own module namespace
and lives in `GNC/Verification/`.

Manuscripts, coverage ledgers, reviews, figures and experiments live in a
separate papers repository, grouped by paper. General mathematics cannot import application
models. Source-module dependencies define this boundary even when an
application theorem extends an existing mathematical namespace.

The mathematical scope is broader than SE₂(3): general block matrices,
nilpotent summation, mixed linear ODEs, matrix exponentials, and then SEₙ(3).
The present exponential theorem supports arbitrary finite translation columns;
the full manifold/tangent construction currently specializes to SE₂(3).
Do not advertise a general SEₙ(3) Lie-group instance until that generalization
is implemented and checked.

## Where it belongs in mathlib

The core should be distributed across existing mathematical areas, not put
entirely inside a new application-specific Lie-group sublibrary.
The following are proposed locations, subject to maintainer agreement.

| Result | Existing area / proposed extension |
| --- | --- |
| Block powers and finite nilpotent sums | Data/Matrix/Block and LinearAlgebra/Matrix/Block, or a small adjacent file |
| Polynomial annihilation and minimal-polynomial consequences | LinearAlgebra/Matrix and polynomial evaluation APIs |
| Block exponential and analytic coefficients | Analysis/Normed/Algebra/MatrixExponential, potentially an adjacent BlockExponential file |
| Mixed flow X′ = MX + XN and continuous linear flows | Analysis/ODE and normed-algebra calculus |
| SO(3), semidirect-product group construction | Existing orthogonal/unitary groups and GroupTheory/SemidirectProduct |
| Smooth SEₙ(3) structure | Geometry/Manifold/Algebra, using LieGroup |
| Tangent Lie algebra and matrix identification | Geometry/Manifold/GroupLieAlgebra and Algebra/Lie |
| Magnus finite polynomial coefficients | Polynomial and associative/Lie algebra APIs, with analytic Magnus theory in Analysis |
| HCW specializations, fixed-wing models, reviewer counterexamples | GNC.Applications, downstream of the general mathematics |

These recommendations use the pinned release's source layout and the current
[mathlib contribution guide](https://leanprover-community.github.io/contribute/index.html).
The guide welcomes extensions to existing theory and also recommends standalone
libraries where specialized material or maintainer coverage makes that preferable.
Final filenames and abstraction choices need review against the then-current
upstream checkout.

## Dependency architecture

The DynamicalSystems assessment in the companion papers repository
recommends keeping GNC separate and adding a narrow bridge for generic
stability, local signal spaces and small gain. Our v4.29.1 mathlib pin remains
unchanged. Their v4.33.0 source is pinned as a review artifact only; it includes
the relevant L-infinity result but needs a common released toolchain before
it can be imported. No bridge or upstream proof audit is claimed yet.

General control certificates can fit DynamicalSystems; elementary matrix,
analysis and Lie-group infrastructure should still target existing mathlib
areas. Spacecraft and aircraft application proofs stay in GNC.Applications.

The source areas are Algebra, Analysis, Lie, Dynamics, Estimation,
Preintegration, Magnus, Planning, Control and Applications. The structure
check enforces complete exports, the core/application boundary and document
links: `nix develop --command python scripts/check_structure.py`.
Further API refinement is appropriate before upstreaming.

1. **Algebra**: generalize finite block identities to the weakest useful scalar
   assumptions. They should not import manifold theory or all tactics.
2. **Analysis**: exponential and ODE results import algebra and relevant mathlib
   calculus. General Banach-algebra theorems should not depend on Vec3 or SE₂(3).
3. **Geometry**: build SEₙ(3) as the appropriate semidirect product, then show
   compatibility with its faithful block-matrix representation. Reuse the
   existing special orthogonal group and manifold/tangent infrastructure.
4. **Preintegration**: specialize the general exponential to the cubic skew
   identity and nilpotent translation/time blocks.
5. **Applications**: spacecraft, aircraft, uncertainty, control, and reviews
   import the library. The dependency must never point back from general
   mathematics into a spacecraft model.

Paper equation numbers and author-specific names belong in docstrings or
application aliases. Public theorem names should follow
[mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html).
The existing declaration named block_minimal_relation proves an annihilating
relation, not minimality; rename it accordingly during extraction.

## First contribution sequence

1. A small block-power theorem with no project dependencies, minimal imports,
   generalized scalars, clear edge cases, and mathlib-style names.
2. Nilpotent finite-sum truncation/factorization and the resulting annihilator.
3. General mixed-flow derivative/uniqueness or missing reusable linear-ODE lemmas.
4. Block-exponential formulas, including zero-rate behavior and analytic
   coefficient specifications.
5. Semidirect-product manifold infrastructure if absent, followed by SEₙ(3)
   and the tangent/matrix Lie-algebra identification.
6. Jacobian and principal-log results after the foundational API is agreed.

Do not send the complete research repository as one PR.
An upstream proof should use established mathlib results (including
Cayley–Hamilton), generalize only where useful, and carry no custom axioms.
Run the relevant upstream style/import checks as well as the kernel build.

## Reproducible release

The released Lean/mathlib flake is locked. All mathematics and application
certificates are freshly rebuilt by the release check, reusing only released
dependency artifacts. There are no compatibility aliases for previous project
names or module locations. Upstream submission remains separate work;
individual results must be adapted to the upstream version and contribution
requirements at submission time.
