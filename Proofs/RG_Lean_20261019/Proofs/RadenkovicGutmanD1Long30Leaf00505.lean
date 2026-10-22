/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00505 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2811177669471742007069813977907200000000000 18552015780525929400044196123850479501312 24347396528593747963042332672000000000000))
theorem leaf00505_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2811177669471742007069813977907200000000000 18552015780525929400044196123850479501312 24347396528593747963042332672000000000000 raw00505=true := by decide +kernel
#print axioms leaf00505_raw
theorem leaf00505_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00505=true := by decide +kernel
#print axioms leaf00505_rectangular
def affine00505 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00505 (IntegerComputedClassCell.leftNumerator ![(11/800),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/800),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00505_transform : affine00505=(NestedInteger.clearedAll 3 raw00505 (IntegerComputedClassCell.leftNumerator ![(11/800),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/800),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00505_transform
theorem leaf00505_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00505=true := by decide +kernel
#print axioms leaf00505_sign
theorem leaf00505_log : RationalLog.accepts (16086585/4294967296) (-5999225001/2147483648) 9 8=true := by decide +kernel
#print axioms leaf00505_log
def leaf00505 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (761971234121/1000000000000) (16086585/4294967296) (-5999225001/2147483648) 9 8 ![60,0,4] ![(11/800),0,0] ![(1/3200),1,(1/16)] affine00505
theorem leaf00505_checked : FastNestedCellData.accepts 1 2 4 leaf00505=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (761971234121/1000000000000) (16086585/4294967296) (-5999225001/2147483648) 9 8 ![60,0,4] ![(11/800),0,0] ![(1/3200),1,(1/16)] 2811177669471742007069813977907200000000000 18552015780525929400044196123850479501312 24347396528593747963042332672000000000000 raw00505 affine00505
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00505_raw leaf00505_rectangular
    leaf00505_transform leaf00505_sign leaf00505_log
#print axioms leaf00505_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
