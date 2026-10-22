/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00230 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 657374002855338318592212992000000000000 488248918715476653512569540237238206464 3344941599211603022925791232000000000000))
theorem leaf00230_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 657374002855338318592212992000000000000 488248918715476653512569540237238206464 3344941599211603022925791232000000000000 raw00230=true := by decide +kernel
#print axioms leaf00230_raw
theorem leaf00230_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00230=true := by decide +kernel
#print axioms leaf00230_rectangular
def affine00230 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00230 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00230_transform : affine00230=(NestedInteger.clearedAll 3 raw00230 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00230_transform
theorem leaf00230_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00230=true := by decide +kernel
#print axioms leaf00230_sign
theorem leaf00230_log : RationalLog.accepts (1391831833/2147483648) (-931312187/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00230_log
def leaf00230 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (4561448461/31250000000) (1391831833/2147483648) (-931312187/4294967296) 1 8 ![52,0,4] ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00230
theorem leaf00230_checked : FastNestedCellData.accepts 1 0 4 leaf00230=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (4561448461/31250000000) (1391831833/2147483648) (-931312187/4294967296) 1 8 ![52,0,4] ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)] 657374002855338318592212992000000000000 488248918715476653512569540237238206464 3344941599211603022925791232000000000000 raw00230 affine00230
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00230_raw leaf00230_rectangular
    leaf00230_transform leaf00230_sign leaf00230_log
#print axioms leaf00230_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
