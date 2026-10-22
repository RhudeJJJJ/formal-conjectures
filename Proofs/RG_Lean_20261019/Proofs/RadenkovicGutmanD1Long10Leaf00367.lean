/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00367 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 508698762916723335091995017216000000000000 438010441309441625281581392522368744685568 992712571449009542701460226048000000000000))
theorem leaf00367_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 508698762916723335091995017216000000000000 438010441309441625281581392522368744685568 992712571449009542701460226048000000000000 raw00367=true := by decide +kernel
#print axioms leaf00367_raw
theorem leaf00367_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00367=true := by decide +kernel
#print axioms leaf00367_rectangular
def affine00367 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00367 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf00367_transform : affine00367=(NestedInteger.clearedAll 3 raw00367 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00367_transform
theorem leaf00367_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00367=true := by decide +kernel
#print axioms leaf00367_sign
theorem leaf00367_log : RationalLog.accepts (2565970163/4294967296) (-1106184545/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00367_log
def leaf00367 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (110306460779/250000000000) (2565970163/4294967296) (-1106184545/4294967296) 1 8 ![52,0,4] ![(41/160),0,(1/4)] ![(3/160),1,(1/4)] affine00367
theorem leaf00367_checked : FastNestedCellData.accepts 1 0 4 leaf00367=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (110306460779/250000000000) (2565970163/4294967296) (-1106184545/4294967296) 1 8 ![52,0,4] ![(41/160),0,(1/4)] ![(3/160),1,(1/4)] 508698762916723335091995017216000000000000 438010441309441625281581392522368744685568 992712571449009542701460226048000000000000 raw00367 affine00367
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00367_raw leaf00367_rectangular
    leaf00367_transform leaf00367_sign leaf00367_log
#print axioms leaf00367_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
