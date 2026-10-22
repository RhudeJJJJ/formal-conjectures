/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00374 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1255537666067257146263103078400000000000 1216495720883480526498230860304772759552 3490845283792650753282146304000000000000))
theorem leaf00374_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1255537666067257146263103078400000000000 1216495720883480526498230860304772759552 3490845283792650753282146304000000000000 raw00374=true := by decide +kernel
#print axioms leaf00374_raw
theorem leaf00374_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00374=true := by decide +kernel
#print axioms leaf00374_rectangular
def affine00374 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00374 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/2)] ![(3/80),1,(1/2)]))
theorem leaf00374_transform : affine00374=(NestedInteger.clearedAll 3 raw00374 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/2)] ![(3/80),1,(1/2)])) := by decide +kernel
#print axioms leaf00374_transform
theorem leaf00374_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00374=true := by decide +kernel
#print axioms leaf00374_sign
theorem leaf00374_log : RationalLog.accepts (1542999005/2147483648) (-709891197/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00374_log
def leaf00374 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (21780106643/62500000000) (1542999005/2147483648) (-709891197/4294967296) 1 8 ![52,0,4] ![(5/16),0,(1/2)] ![(3/80),1,(1/2)] affine00374
theorem leaf00374_checked : FastNestedCellData.accepts 1 0 4 leaf00374=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (21780106643/62500000000) (1542999005/2147483648) (-709891197/4294967296) 1 8 ![52,0,4] ![(5/16),0,(1/2)] ![(3/80),1,(1/2)] 1255537666067257146263103078400000000000 1216495720883480526498230860304772759552 3490845283792650753282146304000000000000 raw00374 affine00374
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00374_raw leaf00374_rectangular
    leaf00374_transform leaf00374_sign leaf00374_log
#print axioms leaf00374_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
