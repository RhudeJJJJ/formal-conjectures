/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00100 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 89085129099772059189248000000000000 74041050738213969112682384745037824 913833734564654154252288000000000000))
theorem leaf00100_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 89085129099772059189248000000000000 74041050738213969112682384745037824 913833734564654154252288000000000000 raw00100=true := by decide +kernel
#print axioms leaf00100_raw
theorem leaf00100_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00100=true := by decide +kernel
#print axioms leaf00100_rectangular
def affine00100 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00100 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00100_transform : affine00100=(NestedInteger.clearedAll 3 raw00100 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00100_transform
theorem leaf00100_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00100=true := by decide +kernel
#print axioms leaf00100_sign
theorem leaf00100_log : RationalLog.accepts (806181/1048576) (-564530643/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00100_log
def leaf00100 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (81022452923/1000000000000) (806181/1048576) (-564530643/4294967296) 1 8 ![52,0,4] ![(17/1600),0,(1/4)] ![(1/3200),1,(1/4)] affine00100
theorem leaf00100_checked : FastNestedCellData.accepts 1 0 4 leaf00100=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (81022452923/1000000000000) (806181/1048576) (-564530643/4294967296) 1 8 ![52,0,4] ![(17/1600),0,(1/4)] ![(1/3200),1,(1/4)] 89085129099772059189248000000000000 74041050738213969112682384745037824 913833734564654154252288000000000000 raw00100 affine00100
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00100_raw leaf00100_rectangular
    leaf00100_transform leaf00100_sign leaf00100_log
#print axioms leaf00100_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
