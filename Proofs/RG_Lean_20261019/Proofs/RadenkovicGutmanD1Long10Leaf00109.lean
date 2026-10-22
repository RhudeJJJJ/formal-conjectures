/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00109 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 396019293716634315087937536000000000000 324401164682972779561097939805177643008 3689145926890543064062885888000000000000))
theorem leaf00109_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 396019293716634315087937536000000000000 324401164682972779561097939805177643008 3689145926890543064062885888000000000000 raw00109=true := by decide +kernel
#print axioms leaf00109_raw
theorem leaf00109_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00109=true := by decide +kernel
#print axioms leaf00109_rectangular
def affine00109 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00109 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00109_transform : affine00109=(NestedInteger.clearedAll 3 raw00109 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00109_transform
theorem leaf00109_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00109=true := by decide +kernel
#print axioms leaf00109_sign
theorem leaf00109_log : RationalLog.accepts (1616938109/2147483648) (-609375269/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00109_log
def leaf00109 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (2747935863/31250000000) (1616938109/2147483648) (-609375269/4294967296) 1 8 ![52,0,4] ![(37/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00109
theorem leaf00109_checked : FastNestedCellData.accepts 1 0 4 leaf00109=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (2747935863/31250000000) (1616938109/2147483648) (-609375269/4294967296) 1 8 ![52,0,4] ![(37/3200),0,(1/4)] ![(1/3200),1,(1/4)] 396019293716634315087937536000000000000 324401164682972779561097939805177643008 3689145926890543064062885888000000000000 raw00109 affine00109
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00109_raw leaf00109_rectangular
    leaf00109_transform leaf00109_sign leaf00109_log
#print axioms leaf00109_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
