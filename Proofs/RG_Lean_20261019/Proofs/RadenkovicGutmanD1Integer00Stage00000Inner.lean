/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Integer00Stage00000Raw
namespace Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def inner00000 : NestedInteger.Poly 3 := rg_integer_data% (IntegerAffineStages.inner raw00000 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.denominator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]))
theorem leaf00000_inner : inner00000=(IntegerAffineStages.inner raw00000 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.denominator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)])) := by decide +kernel
#print axioms leaf00000_inner
end Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
