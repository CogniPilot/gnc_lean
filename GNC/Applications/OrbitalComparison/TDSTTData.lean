import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Prediction
import GNC.Applications.OrbitalComparison.TDSTTData.Lie2.Prediction
import GNC.Applications.OrbitalComparison.TDSTTData.FullCartesian3.Prediction

/-! Polynomial queries derived from the modern TDSTT2 screen. Both charts
include the retained rank-two factorization, exact zero initial errors and
candidate/kinematic ball ranges. Both `physical_prediction` theorems compose
the full residual, scalar-radius constraint, existence and error envelope
for the delivered queries. The full cubic Cartesian refinement also has
its own physical certificate and is exported here. This does not certify the numerical
generator, the raw solver interpolant, or floating-point query evaluation. -/
