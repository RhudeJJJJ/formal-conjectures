/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverageComplete
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteTransfer
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteTransfer
theorem residual_cases_of_certificates (hcertificates : Certificates) :
    DegreeOneMiddleAnchors.ResidualCases :=
  residual_cases DegreeOneMiddleResidualFiniteKeys.parameter_coverage hcertificates
#print axioms residual_cases_of_certificates
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteTransfer
