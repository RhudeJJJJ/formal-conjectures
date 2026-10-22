/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00121 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 30282609380391149845902000128000000000000 23837467500124765462899540329096892383232 226885409304065024081616961536000000000000))
theorem leaf00121_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 30282609380391149845902000128000000000000 23837467500124765462899540329096892383232 226885409304065024081616961536000000000000 raw00121=true := by decide +kernel
#print axioms leaf00121_raw
theorem leaf00121_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00121=true := by decide +kernel
#print axioms leaf00121_rectangular
def affine00121 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00121 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00121_transform : affine00121=(NestedInteger.clearedAll 3 raw00121 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00121_transform
theorem leaf00121_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00121=true := by decide +kernel
#print axioms leaf00121_sign
theorem leaf00121_log : RationalLog.accepts (1529710651/2147483648) (-728465487/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00121_log
def leaf00121 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (26265976703/250000000000) (1529710651/2147483648) (-728465487/4294967296) 1 8 ![52,0,4] ![(11/800),0,(1/4)] ![(1/1600),1,(1/4)] affine00121
theorem leaf00121_checked : FastNestedCellData.accepts 1 0 4 leaf00121=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (26265976703/250000000000) (1529710651/2147483648) (-728465487/4294967296) 1 8 ![52,0,4] ![(11/800),0,(1/4)] ![(1/1600),1,(1/4)] 30282609380391149845902000128000000000000 23837467500124765462899540329096892383232 226885409304065024081616961536000000000000 raw00121 affine00121
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00121_raw leaf00121_rectangular
    leaf00121_transform leaf00121_sign leaf00121_log
#print axioms leaf00121_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
