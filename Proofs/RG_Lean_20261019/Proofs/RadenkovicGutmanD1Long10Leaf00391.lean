/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00391 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 7695628463483412260222664704000000000000 9716004406842963362400494228114226806784 40433454715585354679227252736000000000000))
theorem leaf00391_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 7695628463483412260222664704000000000000 9716004406842963362400494228114226806784 40433454715585354679227252736000000000000 raw00391=true := by decide +kernel
#print axioms leaf00391_raw
theorem leaf00391_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00391=true := by decide +kernel
#print axioms leaf00391_rectangular
def affine00391 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00391 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf00391_transform : affine00391=(NestedInteger.clearedAll 3 raw00391 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00391_transform
theorem leaf00391_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00391=true := by decide +kernel
#print axioms leaf00391_sign
theorem leaf00391_log : RationalLog.accepts (2185989507/2147483648) (4770589/536870912) 0 8=true := by decide +kernel
#print axioms leaf00391_log
def leaf00391 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (60074043111/250000000000) (2185989507/2147483648) (4770589/536870912) 0 8 ![52,0,4] ![(9/16),0,(1/2)] ![(1/16),1,(1/4)] affine00391
theorem leaf00391_checked : FastNestedCellData.accepts 1 0 4 leaf00391=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (60074043111/250000000000) (2185989507/2147483648) (4770589/536870912) 0 8 ![52,0,4] ![(9/16),0,(1/2)] ![(1/16),1,(1/4)] 7695628463483412260222664704000000000000 9716004406842963362400494228114226806784 40433454715585354679227252736000000000000 raw00391 affine00391
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00391_raw leaf00391_rectangular
    leaf00391_transform leaf00391_sign leaf00391_log
#print axioms leaf00391_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
