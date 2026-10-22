/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00051 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2474970337929179989595574501376000000000000 592821817574297749424468512191834750976 4418490267343688646541705216000000000000))
theorem leaf00051_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2474970337929179989595574501376000000000000 592821817574297749424468512191834750976 4418490267343688646541705216000000000000 raw00051=true := by decide +kernel
#print axioms leaf00051_raw
theorem leaf00051_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00051=true := by decide +kernel
#print axioms leaf00051_rectangular
def affine00051 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00051 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/1600),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00051_transform : affine00051=(NestedInteger.clearedAll 3 raw00051 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/1600),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00051_transform
theorem leaf00051_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00051=true := by decide +kernel
#print axioms leaf00051_sign
theorem leaf00051_log : RationalLog.accepts (907061/4294967296) (-9086803263/2147483648) 13 8=true := by decide +kernel
#print axioms leaf00051_log
def leaf00051 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (134168410861/1000000000000) (907061/4294967296) (-9086803263/2147483648) 13 8 ![52,0,4] ![(9/1600),0,0] ![(1/3200),1,(1/4)] affine00051
theorem leaf00051_checked : FastNestedCellData.accepts 1 0 4 leaf00051=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (134168410861/1000000000000) (907061/4294967296) (-9086803263/2147483648) 13 8 ![52,0,4] ![(9/1600),0,0] ![(1/3200),1,(1/4)] 2474970337929179989595574501376000000000000 592821817574297749424468512191834750976 4418490267343688646541705216000000000000 raw00051 affine00051
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00051_raw leaf00051_rectangular
    leaf00051_transform leaf00051_sign leaf00051_log
#print axioms leaf00051_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
