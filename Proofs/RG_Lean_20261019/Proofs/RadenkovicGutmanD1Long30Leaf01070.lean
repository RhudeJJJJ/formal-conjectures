/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01070 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1608044763753053187127747018752000000000000 1644939382158736035988424833277890356314112 4717495508120692658116833050624000000000000))
theorem leaf01070_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1608044763753053187127747018752000000000000 1644939382158736035988424833277890356314112 4717495508120692658116833050624000000000000 raw01070=true := by decide +kernel
#print axioms leaf01070_raw
theorem leaf01070_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01070=true := by decide +kernel
#print axioms leaf01070_rectangular
def affine01070 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01070 (IntegerComputedClassCell.leftNumerator ![(7/20),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/20),0,0] ![(3/160),1,(1/16)]))
theorem leaf01070_transform : affine01070=(NestedInteger.clearedAll 3 raw01070 (IntegerComputedClassCell.leftNumerator ![(7/20),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/20),0,0] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01070_transform
theorem leaf01070_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01070=true := by decide +kernel
#print axioms leaf01070_sign
theorem leaf01070_log : RationalLog.accepts (1628807551/2147483648) (-593668835/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01070_log
def leaf01070 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (348689125263/1000000000000) (1628807551/2147483648) (-593668835/4294967296) 1 8 ![60,0,4] ![(7/20),0,0] ![(3/160),1,(1/16)] affine01070
theorem leaf01070_checked : FastNestedCellData.accepts 1 2 4 leaf01070=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (348689125263/1000000000000) (1628807551/2147483648) (-593668835/4294967296) 1 8 ![60,0,4] ![(7/20),0,0] ![(3/160),1,(1/16)] 1608044763753053187127747018752000000000000 1644939382158736035988424833277890356314112 4717495508120692658116833050624000000000000 raw01070 affine01070
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01070_raw leaf01070_rectangular
    leaf01070_transform leaf01070_sign leaf01070_log
#print axioms leaf01070_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
