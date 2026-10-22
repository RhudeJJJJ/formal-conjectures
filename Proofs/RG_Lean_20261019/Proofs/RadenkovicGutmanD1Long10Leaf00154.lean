/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00154 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 43862115995839148899132506112000000000000 31541110267682917397977406378691920920576 207265560958328273863664730112000000000000))
theorem leaf00154_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 43862115995839148899132506112000000000000 31541110267682917397977406378691920920576 207265560958328273863664730112000000000000 raw00154=true := by decide +kernel
#print axioms leaf00154_raw
theorem leaf00154_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00154=true := by decide +kernel
#print axioms leaf00154_rectangular
def affine00154 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00154 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00154_transform : affine00154=(NestedInteger.clearedAll 3 raw00154 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00154_transform
theorem leaf00154_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00154=true := by decide +kernel
#print axioms leaf00154_sign
theorem leaf00154_log : RationalLog.accepts (2680574921/4294967296) (-506175493/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00154_log
def leaf00154 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (19022160581/125000000000) (2680574921/4294967296) (-506175493/2147483648) 1 8 ![52,0,4] ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00154
theorem leaf00154_checked : FastNestedCellData.accepts 1 0 4 leaf00154=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (19022160581/125000000000) (2680574921/4294967296) (-506175493/2147483648) 1 8 ![52,0,4] ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)] 43862115995839148899132506112000000000000 31541110267682917397977406378691920920576 207265560958328273863664730112000000000000 raw00154 affine00154
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00154_raw leaf00154_rectangular
    leaf00154_transform leaf00154_sign leaf00154_log
#print axioms leaf00154_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
