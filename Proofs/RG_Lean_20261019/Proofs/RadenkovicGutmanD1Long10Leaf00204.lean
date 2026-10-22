/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00204 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 10542399665347302234878015176704000000000000 281095914226346299424508208464179132104704 491852382237303522676090863616000000000000))
theorem leaf00204_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 10542399665347302234878015176704000000000000 281095914226346299424508208464179132104704 491852382237303522676090863616000000000000 raw00204=true := by decide +kernel
#print axioms leaf00204_raw
theorem leaf00204_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00204=true := by decide +kernel
#print axioms leaf00204_rectangular
def affine00204 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00204 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(109/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00204_transform : affine00204=(NestedInteger.clearedAll 3 raw00204 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(109/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00204_transform
theorem leaf00204_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00204=true := by decide +kernel
#print axioms leaf00204_sign
theorem leaf00204_log : RationalLog.accepts (72871759/4294967296) (-8754213115/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00204_log
def leaf00204 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (571504631019/1000000000000) (72871759/4294967296) (-8754213115/4294967296) 6 8 ![52,0,4] ![(109/3200),0,0] ![(3/3200),1,(1/4)] affine00204
theorem leaf00204_checked : FastNestedCellData.accepts 1 0 4 leaf00204=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (571504631019/1000000000000) (72871759/4294967296) (-8754213115/4294967296) 6 8 ![52,0,4] ![(109/3200),0,0] ![(3/3200),1,(1/4)] 10542399665347302234878015176704000000000000 281095914226346299424508208464179132104704 491852382237303522676090863616000000000000 raw00204 affine00204
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00204_raw leaf00204_rectangular
    leaf00204_transform leaf00204_sign leaf00204_log
#print axioms leaf00204_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
