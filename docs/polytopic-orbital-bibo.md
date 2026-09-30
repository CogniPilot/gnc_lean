# Polytopic LMI/BIBO tubes with the orbital gravity remainder

The generic regional theorem and the physical gravity-to-sector bridge are
kernel checked in `GNC.Control.PolytopicResidualTube` and
`GNC.Dynamics.OrbitalPolytopicTube`. They reuse existing results rather than
introducing a new LMI or Lyapunov theory. This is a **conditional local
disturbance certificate**, not a newly synthesized spacecraft controller.

## Exact state-dependent coefficient form

The same model now has the checked representation

    z_dot = [A₀(t) + ΔA(t,z)] z + B d,
    ΔA(t,0) = 0,
    norm(ΔA(t,z)) <= c norm(z).

`Analysis/VanishingCoefficient.lean` constructs a witness from the quadratic
residual: for nonzero z, use `r(t,z) zᵀ / norm(z)^2`, and use zero at z=0.
Its product with z is exactly r(t,z), and its operator norm has the stated
bound. This is an existence proof, not a numerically recommended formula.
The bound is a linear modulus relative to the origin; a general pairwise
Lipschitz claim needs additional regularity. The group error tends to
identity, while its logarithm z tends to zero.

`Dynamics/OrbitalGravityCoefficient.lean` composes this construction with
the **actual** orbital gravity remainder and its scaling gains below.
`VanishingCoefficient.storage_supply` directly converts the coefficient
bound to the regional storage inequality used by the tube theorem.

For fixed certificate data, define `k = 2 norm(P) c / m` and choose
`rho = m R^2`. The strict budget is

    nu delta^2 < F(R),     F(R) = m R^2 (alpha - k R).

`Control/ResidualBudget.lean` proves the exact identity

    4 m alpha^3 / (27 k^2) - F(R)
      = m k (R - 2 alpha/(3 k))^2 (R + alpha/(3 k)).

For positive alpha, m, k this proves the maximum over nonnegative radii,
attained at `R = 2 alpha/(3 k)`. The budget is nondecreasing up to this
radius. Thus a domain cap selects the smaller of that radius and the cap,
subject also to initial-set containment. All residual constants, including
the gravity-domain D used to obtain c, must be fixed over the radius range.
This optimizes a sufficient budget for a fixed certificate; it does not
solve controller synthesis or optimize the true robust stability margin.

## What already existed, and what changed

- `Control/LMI.lean`: exact matrix semidefinite certificates via weighted
  Gram factors, conic combinations, and analytic dissipative blocks.
- `Control/PolytopicTube.lean`: vertex supply extends to convex combinations;
  derivative of the actual quadratic storage; a reachable-set comparison
  whose trajectory predicate explicitly includes region membership.
- `Control/ReferenceTube.lean`: first-exit/boundary invariance, independently
  of any assumed trajectory containment.
- `Control/OutputTube.lean`: output support bounds and nonlinear set images.
- New composition: vertex supply plus a *regional* nonlinear sector proves
  the region invariant, then establishes the transient disturbance bound.
- New orbital bridge: the actual log-gravity residual supplies that sector
  with explicit coordinate and acceleration-injection gains.

## Mathematical contract

Use a consistently scaled Euclidean error state z and an existing classical
trajectory solving

    z_dot = A(t) z + B d(t) + r(t,z),
    A(t) = sum_i w_i(t) A_i,   w_i >= 0,   sum_i w_i = 1,
    norm(d(t)) <= delta.

The weights can be arbitrary time histories, including histories induced
by a state-dependent convex enclosure. Proving that the actual A belongs
to the vertex hull is required: a time sample grid does not establish it.
This also applies to a verified closed-loop A. It does not manufacture a
stabilizing controller for the open-loop orbital model.

Take symmetric P and V(z) = z' P z, with m norm(z)^2 <= V(z), m > 0.
For every vertex assume the common quadratic supply

    2 z' P (A_i z + B d) + alpha V(z) <= nu norm(d)^2.

In finite-dimensional Euclidean coordinates this is the standard block LMI

    [ A_i' P + P A_i + alpha P     P B  ] <= 0.
    [ B' P                       -nu I ]

`certificate` consumes the universal quadratic-form inequality. Existing
`LMI.of_weighted_gram` checks matrix certificates separately; no SDP solver
status or floating eigenvalue test is accepted as a proof. A proposed matrix
certificate still has to be connected to its particular system's quadratic
form. The new theorem is not an automatic SDP solver or synthesis procedure.

Suppose the nonlinear residual has a proved bound only on norm(z) <= R:

    norm(r(t,z)) <= c norm(z)^2,     c >= 0.

Choose an energy radius rho satisfying rho <= m R^2. On V <= rho:

    norm(r) <= c R norm(z),
    2 z' P r <= gamma V,
    gamma = 2 norm(P) c R / m.

This follows from Cauchy–Schwarz, the operator norm, and coercivity. Directional
or energy-neutral residual estimates can replace this conservative norm
estimate; the main theorem accepts a proved supply bound directly.

Define beta = alpha - gamma. The computable sufficient conditions are

    beta > 0,
    nu delta^2 < beta rho,
    V(z(0)) <= rho.

Then, on every interval on which the stipulated classical trajectory exists,

    V(z(t)) <= rho,
    V(z(t)) <= V(z(0)) exp(-beta t)
                 + (nu delta^2 / beta) (1 - exp(-beta t)).

The strict inequality is an actual inward dissipation condition. Its margin
is beta rho - nu delta^2; there is no separately invented numerical allowance.
The equality case is not asserted by this theorem. No fixed-point iteration
is prescribed: propose P and R/rho, evaluate gamma, and check the inequalities.
Finding feasible P/radii may still require an optimization or search.

Proof: vertex convexity gives the linear supply; the regional sector reduces
its decay from alpha to beta. At a first boundary contact V=rho, the derivative
is strictly negative. Mathlib's boundary theorem prevents escape. Grönwall
then applies on the now-proved region and gives the displayed transient bound.

For an output with norm(h(z)) <= L norm(z) on the ball, `output_bound`
proves norm(h(z(t))) <= L R. This includes a nonlinear output map if its
regional gain has been proved. A linear output may use its operator norm;
`OutputTube` also retains directional information instead of replacing every
output by a ball. Uniform hypotheses and global existence extend the result
to all times, but the theorem does not prove global existence or feasibility
for arbitrary disturbance amplitudes. A finite-horizon orbital tube alone
does not imply infinite-horizon BIBO stability.

## Actual orbital remainder and coordinate gains

The exact shared-input orbital equation gives the remainder

    r_g = (J^-1 G J - G) rho_p
          + J^-1 Rbar' [g(pbar + Rbar J rho_p) - g(pbar)
                        - Dg(pbar) Rbar J rho_p].

There are both angle–position and position-squared contributions. On the
one-radian chart and spatial region D < r_star <= norm(pbar), the existing
physical theorem bounds both. Let encoding into physical log coordinates
and acceleration injection satisfy

    norm(rho_p) <= ell_p norm(z),
    norm(phi)   <= ell_phi norm(z),
    norm(inject(v)) <= ell_f norm(v).

The new `gravity_quadratic` theorem proves

    norm(inject(r_g)) <= c(t) norm(z)^2,
    c(t) = ell_f [2 mu ell_phi ell_p / norm(pbar(t))^3
                  + 4 mu ell_p^2 / (r_star - D)^4],

provided ell_p R <= D and ell_phi R <= 1. `gravity_supply` composes this
actual physical bound with the storage-sector result. A uniform bound on
c(t) gives the constant gamma required by `certificate`. The library's
`LogState` uses a product norm; the explicit encoding and injection gains
prevent silently identifying it with the quadratic storage's Euclidean norm.

What remains for a mission: a realizable closed-loop error ODE; its vertex
enclosure; feasible P, alpha, nu; disturbance bounds including all log-Jacobian
factors; initial-set inclusion; and physical reconstruction/output bounds.
The shared-input ACC example does not supply these controller-dependent items.
No infinite-horizon stability claim is made for that open-loop burn.

## Checked declarations

| Declaration | Guarantee |
|---|---|
| `PolytopicResidualTube.quadratic_sector` | Quadratic remainder to regional norm sector |
| `.sector_supply` | Coercivity and Cauchy–Schwarz give storage loss |
| `.sublevel_norm` | Ellipsoid is inside the residual-validity ball |
| `.quadratic_supply` | Complete nonlinear supply on the energy sublevel |
| `.certificate` | First-exit invariance and transient disturbance bound |
| `.output_bound` | Regional output gain gives a bounded physical output |
| `OrbitalPolytopicTube.gravity_quadratic` | Physical orbital residual with coordinate gains |
| `.gravity_supply` | Orbital residual to quadratic-storage loss |

## Powered attitude/translation cascade baseline

`Control.OrbitalCascadeTube` now supplies a strong Cartesian translation
baseline, to avoid claiming a coordinate advantage against an unnecessarily
weak comparator. For scaled errors `x=e/L`, `y=x+tau*edot/L`, normalized time
`s=t/tau`, and `V=norm(x)^2+norm(y)^2`, its exact PD square identity gives
linear decay 1/2 and input supply `2 norm(d)^2`. The actual gravity gradient
and quadratic remainder consume `K+C R` of that decay. A strict budget closes
the region by first exit. `scaled_gravity_bounds` derives K and C from the
physical inverse-square field and `physical_feedback_identity` checks the
feedback scaling algebra.

`Control.AttitudeThrustBridge` connects the existing exact log/rate energy to
physical thrust error for all attitude axes, without a small-angle force
approximation. `force_square_bound` preserves a time-dependent energy bound
instead of replacing it by a constant angle cap. Ideal body-frame allocation
of an independent Cartesian correction is also checked.

`Control.DecayingSupplyTube` proves the exact comparison envelope for
`Vdot <= -lambda V + S + H exp(-c t)`, with nonzero lambda and distinct rates.
`OrbitalCascadeTube.transient_certificate` composes it with the invariant
region: first establish containment using the uniform budget, then apply the
sharper supply throughout that proved region. No second assumed tube is used.

`Applications.OrbitalBibo.PoweredReference` checks a constructed radial-thrust
circular reference, its actual gravity/acceleration ODE, radius, and rate.
`CascadeExample` checks exact rational data for a 100 kg example with 20 mN
main thrust and 3 mN independent correction authority. The 12 m region closes;
constant-cap and transient limiting position bounds are below 10.2 m and
6.1 m respectively. Their squared steady supplies have exact ratio 9/25.
The paper reports the more precise numerical radii, 10.127 m and 6.077 m.

The physical attitude chart, classical-solution existence and command
realization remain hypotheses. A single theorem composing the complete
physical spacecraft, its chart continuation, all conversions, and actuator
implementation has not been completed. The simulations are diagnostics.
Neither the cascade refinement nor its example establishes that full
SE2(3) translation coordinates outperform Cartesian coordinates.
