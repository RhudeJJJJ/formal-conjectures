/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00123 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 98209735284794041213684547584000000000000 93388904135437721093478994167997904453632 4385311723208938065431722196992000000000000))
theorem leaf00123_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 98209735284794041213684547584000000000000 93388904135437721093478994167997904453632 4385311723208938065431722196992000000000000 raw00123=true := by decide +kernel
#print axioms leaf00123_raw
theorem leaf00123_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00123=true := by decide +kernel
#print axioms leaf00123_rectangular
def affine00123 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00123 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00123_transform : affine00123=(NestedInteger.clearedAll 3 raw00123 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00123_transform
theorem leaf00123_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00123=true := by decide +kernel
#print axioms leaf00123_sign
theorem leaf00123_log : RationalLog.accepts (1999489099/2147483648) (-153341241/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00123_log
def leaf00123 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (21295841671/1000000000000) (1999489099/2147483648) (-153341241/4294967296) 1 8 ![60,0,4] ![(11/4000),0,(1/4)] ![(3/32000),1,(1/4)] affine00123
theorem leaf00123_checked : FastNestedCellData.accepts 1 2 4 leaf00123=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (21295841671/1000000000000) (1999489099/2147483648) (-153341241/4294967296) 1 8 ![60,0,4] ![(11/4000),0,(1/4)] ![(3/32000),1,(1/4)] 98209735284794041213684547584000000000000 93388904135437721093478994167997904453632 4385311723208938065431722196992000000000000 raw00123 affine00123
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00123_raw leaf00123_rectangular
    leaf00123_transform leaf00123_sign leaf00123_log
#print axioms leaf00123_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
