/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00342 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 742039224207360093205823488000000000000 310488393537101683914997572037332959232 471105626164918552872615936000000000000))
theorem leaf00342_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 742039224207360093205823488000000000000 310488393537101683914997572037332959232 471105626164918552872615936000000000000 raw00342=true := by decide +kernel
#print axioms leaf00342_raw
theorem leaf00342_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00342=true := by decide +kernel
#print axioms leaf00342_rectangular
def affine00342 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00342 (IntegerComputedClassCell.leftNumerator ![(23/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/160),0,0] ![(1/160),1,(1/4)]))
theorem leaf00342_transform : affine00342=(NestedInteger.clearedAll 3 raw00342 (IntegerComputedClassCell.leftNumerator ![(23/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/160),0,0] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00342_transform
theorem leaf00342_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00342=true := by decide +kernel
#print axioms leaf00342_sign
theorem leaf00342_log : RationalLog.accepts (67701057/268435456) (-1479088745/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00342_log
def leaf00342 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (82382903189/125000000000) (67701057/268435456) (-1479088745/2147483648) 2 8 ![52,0,4] ![(23/160),0,0] ![(1/160),1,(1/4)] affine00342
theorem leaf00342_checked : FastNestedCellData.accepts 1 0 4 leaf00342=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (82382903189/125000000000) (67701057/268435456) (-1479088745/2147483648) 2 8 ![52,0,4] ![(23/160),0,0] ![(1/160),1,(1/4)] 742039224207360093205823488000000000000 310488393537101683914997572037332959232 471105626164918552872615936000000000000 raw00342 affine00342
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00342_raw leaf00342_rectangular
    leaf00342_transform leaf00342_sign leaf00342_log
#print axioms leaf00342_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
