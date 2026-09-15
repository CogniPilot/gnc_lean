import GNC.Applications.OrbitalComparison.SpatialSources
import GNC.Applications.OrbitalComparison.BernsteinCertificate

/-! The checked Bernstein parameter envelope for the spatial physical source.
Only the source polynomial changes from `polynomialRepresentation` to its
order-24 version; the value map and the Bernstein soundness proof are shared.
Candidate coefficients may come from any untrusted approximation procedure.
-/
namespace GNC.OrbitalComparison.SpatialSources
open UniformCertificate WeightedCertificate

noncomputable def polynomial24BernsteinTime : TimeRepresentation polynomial24 where
  envelope := fun p => BernsteinTime.bivariate p (-angle) angle
  nonnegative := fun p => BernsteinTime.bivariate_nonnegative p _ _
  sound := fun p {_ _} ht hθ => BernsteinTime.bivariate_sound p (by norm_num [angle]) ht
    (by simpa only [Rat.cast_neg] using abs_le.mp hθ)

end GNC.OrbitalComparison.SpatialSources
