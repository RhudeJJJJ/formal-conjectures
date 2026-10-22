/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00146 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 105526864277270825727955042304000000000000 90234648029868646944394891526564286038016 1314464228444155340223751913472000000000000))
theorem leaf00146_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 105526864277270825727955042304000000000000 90234648029868646944394891526564286038016 1314464228444155340223751913472000000000000 raw00146=true := by decide +kernel
#print axioms leaf00146_raw
theorem leaf00146_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00146=true := by decide +kernel
#print axioms leaf00146_rectangular
def affine00146 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00146 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00146_transform : affine00146=(NestedInteger.clearedAll 3 raw00146 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00146_transform
theorem leaf00146_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00146=true := by decide +kernel
#print axioms leaf00146_sign
theorem leaf00146_log : RationalLog.accepts (1718326539/2147483648) (-59846585/536870912) 1 8=true := by decide +kernel
#print axioms leaf00146_log
def leaf00146 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (68647473303/1000000000000) (1718326539/2147483648) (-59846585/536870912) 1 8 ![52,0,4] ![(3/160),0,(1/2)] ![(1/1600),1,(1/2)] affine00146
theorem leaf00146_checked : FastNestedCellData.accepts 1 0 4 leaf00146=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (68647473303/1000000000000) (1718326539/2147483648) (-59846585/536870912) 1 8 ![52,0,4] ![(3/160),0,(1/2)] ![(1/1600),1,(1/2)] 105526864277270825727955042304000000000000 90234648029868646944394891526564286038016 1314464228444155340223751913472000000000000 raw00146 affine00146
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00146_raw leaf00146_rectangular
    leaf00146_transform leaf00146_sign leaf00146_log
#print axioms leaf00146_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
