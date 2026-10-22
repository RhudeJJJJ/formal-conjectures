/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00069 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6278307713030345937418557849600000000000 6176370217757859651145672714605306052608 907361712097960970898777309184000000000000))
theorem leaf00069_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6278307713030345937418557849600000000000 6176370217757859651145672714605306052608 907361712097960970898777309184000000000000 raw00069=true := by decide +kernel
#print axioms leaf00069_raw
theorem leaf00069_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00069=true := by decide +kernel
#print axioms leaf00069_rectangular
def affine00069 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00069 (IntegerComputedClassCell.leftNumerator ![(29/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/16000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00069_transform : affine00069=(NestedInteger.clearedAll 3 raw00069 (IntegerComputedClassCell.leftNumerator ![(29/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/16000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00069_transform
theorem leaf00069_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00069=true := by decide +kernel
#print axioms leaf00069_sign
theorem leaf00069_log : RationalLog.accepts (4196665715/4294967296) (-3107627/268435456) 1 8=true := by decide +kernel
#print axioms leaf00069_log
def leaf00069 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3403477431/500000000000) (4196665715/4294967296) (-3107627/268435456) 1 8 ![60,0,4] ![(29/16000),0,(1/2)] ![(1/16000),1,(1/2)] affine00069
theorem leaf00069_checked : FastNestedCellData.accepts 1 2 4 leaf00069=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3403477431/500000000000) (4196665715/4294967296) (-3107627/268435456) 1 8 ![60,0,4] ![(29/16000),0,(1/2)] ![(1/16000),1,(1/2)] 6278307713030345937418557849600000000000 6176370217757859651145672714605306052608 907361712097960970898777309184000000000000 raw00069 affine00069
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00069_raw leaf00069_rectangular
    leaf00069_transform leaf00069_sign leaf00069_log
#print axioms leaf00069_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
