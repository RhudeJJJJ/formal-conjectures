/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00124 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2021626331402047267064583815168000000000000 1576842723357732582749975988927745348337664 14388224821991862458832302112768000000000000))
theorem leaf00124_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2021626331402047267064583815168000000000000 1576842723357732582749975988927745348337664 14388224821991862458832302112768000000000000 raw00124=true := by decide +kernel
#print axioms leaf00124_raw
theorem leaf00124_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00124=true := by decide +kernel
#print axioms leaf00124_rectangular
def affine00124 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00124 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00124_transform : affine00124=(NestedInteger.clearedAll 3 raw00124 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00124_transform
theorem leaf00124_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00124=true := by decide +kernel
#print axioms leaf00124_sign
theorem leaf00124_log : RationalLog.accepts (3019143871/4294967296) (-756924963/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00124_log
def leaf00124 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (109592583023/1000000000000) (3019143871/4294967296) (-756924963/4294967296) 1 8 ![52,0,4] ![(23/1600),0,(1/4)] ![(1/1600),1,(1/4)] affine00124
theorem leaf00124_checked : FastNestedCellData.accepts 1 0 4 leaf00124=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (109592583023/1000000000000) (3019143871/4294967296) (-756924963/4294967296) 1 8 ![52,0,4] ![(23/1600),0,(1/4)] ![(1/1600),1,(1/4)] 2021626331402047267064583815168000000000000 1576842723357732582749975988927745348337664 14388224821991862458832302112768000000000000 raw00124 affine00124
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00124_raw leaf00124_rectangular
    leaf00124_transform leaf00124_sign leaf00124_log
#print axioms leaf00124_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
