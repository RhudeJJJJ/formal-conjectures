/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLongArmPrerequisiteBase
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerBernsteinWeights52
import Proofs.RadenkovicGutmanIntegerBernsteinWeights60
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanIntegerOuterTable

/- This bundle retains exact per-cell identities, row signs, physical covers,
and integral payments. Only proved scalar transformations are shared. -/
#print axioms Gebendorfer.RadenkovicGutman.IntegerPiecewiseCell.accepts_make
#print axioms Gebendorfer.RadenkovicGutman.IntegerOuterTable.checked
#print axioms Gebendorfer.RadenkovicGutman.IntegerBernsteinTable.checked
#print axioms Gebendorfer.RadenkovicGutman.IntegerBernsteinWeights52.row052_identity
#print axioms Gebendorfer.RadenkovicGutman.IntegerBernsteinWeights60.row060_identity
#print axioms Gebendorfer.RadenkovicGutman.IntegerBernsteinWeights88.row088_identity
