/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSharedArmKernelBase
import Proofs.RadenkovicGutmanActualMeanOrigin
import Proofs.RadenkovicGutmanPolynomialPaymentCell
import Proofs.RadenkovicGutmanInversePolynomialNorm
import Proofs.RadenkovicGutmanQuantitativePositiveTail
import Proofs.RadenkovicGutmanBernsteinLogIntegral

/- This endpoint packages the checked prerequisites. Concrete anchor and arm
certificates are separate obligations and are not asserted here. -/
#print axioms Gebendorfer.RadenkovicGutman.ActualMeanOrigin.actual_origin_lower
#print axioms Gebendorfer.RadenkovicGutman.PolynomialPaymentCell.actual_integral_lower
#print axioms Gebendorfer.RadenkovicGutman.GeneralPathPolynomialPayments.actual_norm_lower
#print axioms Gebendorfer.RadenkovicGutman.InversePolynomialNorm.inverse_parameter
#print axioms Gebendorfer.RadenkovicGutman.QuantitativePositiveTail.integral_lower
#print axioms Gebendorfer.RadenkovicGutman.BernsteinLogIntegral.norm_square_log_lower
