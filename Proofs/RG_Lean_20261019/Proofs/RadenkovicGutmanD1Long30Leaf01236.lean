/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01236 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 31300078464336145160188461056000000000000 34308083246179018015137647983688782184448 5054878952004007219065343967232000000000000))
theorem leaf01236_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 31300078464336145160188461056000000000000 34308083246179018015137647983688782184448 5054878952004007219065343967232000000000000 raw01236=true := by decide +kernel
#print axioms leaf01236_raw
theorem leaf01236_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01236=true := by decide +kernel
#print axioms leaf01236_rectangular
def affine01236 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01236 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf01236_transform : affine01236=(NestedInteger.clearedAll 3 raw01236 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf01236_transform
theorem leaf01236_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01236=true := by decide +kernel
#print axioms leaf01236_sign
theorem leaf01236_log : RationalLog.accepts (4675986387/4294967296) (182527931/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01236_log
def leaf01236 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (3393561307/500000000000) (4675986387/4294967296) (182527931/4294967296) 0 8 ![60,0,4] ![(1/4),0,(1/2)] ![(1/64),1,(1/4)] affine01236
theorem leaf01236_checked : FastNestedCellData.accepts 1 2 4 leaf01236=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (3393561307/500000000000) (4675986387/4294967296) (182527931/4294967296) 0 8 ![60,0,4] ![(1/4),0,(1/2)] ![(1/64),1,(1/4)] 31300078464336145160188461056000000000000 34308083246179018015137647983688782184448 5054878952004007219065343967232000000000000 raw01236 affine01236
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01236_raw leaf01236_rectangular
    leaf01236_transform leaf01236_sign leaf01236_log
#print axioms leaf01236_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
