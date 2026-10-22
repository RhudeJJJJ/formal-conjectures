/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00047 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 357352384621955758969742950400000000000 337060570316974302697541761016572936192 13593178491189928160558841856000000000000))
theorem leaf00047_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 357352384621955758969742950400000000000 337060570316974302697541761016572936192 13593178491189928160558841856000000000000 raw00047=true := by decide +kernel
#print axioms leaf00047_raw
theorem leaf00047_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00047=true := by decide +kernel
#print axioms leaf00047_rectangular
def affine00047 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00047 (IntegerComputedClassCell.leftNumerator ![(1/640),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/640),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/640),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00047_transform : affine00047=(NestedInteger.clearedAll 3 raw00047 (IntegerComputedClassCell.leftNumerator ![(1/640),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/640),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/640),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00047_transform
theorem leaf00047_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00047=true := by decide +kernel
#print axioms leaf00047_sign
theorem leaf00047_log : RationalLog.accepts (3953061565/4294967296) (-89070749/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00047_log
def leaf00047 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1549768927/62500000000) (3953061565/4294967296) (-89070749/2147483648) 1 8 ![60,0,4] ![(1/640),0,(1/8)] ![(1/16000),1,(1/8)] affine00047
theorem leaf00047_checked : FastNestedCellData.accepts 1 2 4 leaf00047=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1549768927/62500000000) (3953061565/4294967296) (-89070749/2147483648) 1 8 ![60,0,4] ![(1/640),0,(1/8)] ![(1/16000),1,(1/8)] 357352384621955758969742950400000000000 337060570316974302697541761016572936192 13593178491189928160558841856000000000000 raw00047 affine00047
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00047_raw leaf00047_rectangular
    leaf00047_transform leaf00047_sign leaf00047_log
#print axioms leaf00047_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
