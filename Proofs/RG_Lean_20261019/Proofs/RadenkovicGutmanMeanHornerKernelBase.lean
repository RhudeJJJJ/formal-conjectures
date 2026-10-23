/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMeanPolynomialKernelBase
import Proofs.RadenkovicGutmanFastPolynomialPaymentCell
import Proofs.RadenkovicGutmanRationalIntegralPartition
import Proofs.RadenkovicGutmanMean16PolynomialBase
import Proofs.RadenkovicGutmanMean16Origin
import Proofs.RadenkovicGutmanMean16PositiveTail

/- Checked prerequisites for re-use; concrete anchor assembly remains separate. -/
#print axioms Gebendorfer.RadenkovicGutman.FastPolynomialPaymentCell.actual_integral_lower
#print axioms Gebendorfer.RadenkovicGutman.RationalIntegralPartition.integral_lower
#print axioms Gebendorfer.RadenkovicGutman.RationalIntegralPartition.three_region_lower
#print axioms Gebendorfer.RadenkovicGutman.Mean16PolynomialBase.path_checked
#print axioms Gebendorfer.RadenkovicGutman.Mean16PolynomialBase.norms_checked
#print axioms Gebendorfer.RadenkovicGutman.Mean16Origin.actual_integral
#print axioms Gebendorfer.RadenkovicGutman.Mean16PositiveTail.actual_integral
