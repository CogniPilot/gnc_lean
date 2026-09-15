import GNC.Applications.OrbitalComparison.WeightedCertificate
import GNC.Analysis.BernsteinTime

/-! Bernstein parameter bounders plugged into the same physical certificate.
The stored candidate, physical model, time envelope and nonlinear-gravity
closure are unchanged. Only the bound on each parameter polynomial changes.
-/
namespace GNC.OrbitalComparison.WeightedCertificate
open UniformCertificate

noncomputable def circleBernsteinTime : TimeRepresentation circleRepresentation where
  envelope := fun p => BernsteinTime.circle p angle
  nonnegative := fun p => BernsteinTime.circle_nonnegative p (by norm_num [angle])
  sound := fun p {_ _} ht hθ => BernsteinTime.circle_sound p (by norm_num [angle]) ht hθ

noncomputable def polynomialBernsteinTime : TimeRepresentation polynomialRepresentation where
  envelope := fun p => BernsteinTime.bivariate p (-angle) angle
  nonnegative := fun p => BernsteinTime.bivariate_nonnegative p _ _
  sound := fun p {_ _} ht hθ => BernsteinTime.bivariate_sound p (by norm_num [angle]) ht
    (by simpa only [Rat.cast_neg] using abs_le.mp hθ)

end GNC.OrbitalComparison.WeightedCertificate
