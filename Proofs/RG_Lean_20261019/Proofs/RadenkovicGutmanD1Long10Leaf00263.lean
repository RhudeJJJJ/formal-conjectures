/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00263 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 34406721456277791125212548300800000000000 24090433103683505733241933650716038004736 129157918941267641722184348467200000000000))
theorem leaf00263_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 34406721456277791125212548300800000000000 24090433103683505733241933650716038004736 129157918941267641722184348467200000000000 raw00263=true := by decide +kernel
#print axioms leaf00263_raw
theorem leaf00263_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00263=true := by decide +kernel
#print axioms leaf00263_rectangular
def affine00263 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00263 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00263_transform : affine00263=(NestedInteger.clearedAll 3 raw00263 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00263_transform
theorem leaf00263_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00263=true := by decide +kernel
#print axioms leaf00263_sign
theorem leaf00263_log : RationalLog.accepts (1267232807/2147483648) (-566357093/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00263_log
def leaf00263 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (37303842151/200000000000) (1267232807/2147483648) (-566357093/2147483648) 1 8 ![52,0,4] ![(7/128),0,(1/2)] ![(1/640),1,(1/2)] affine00263
theorem leaf00263_checked : FastNestedCellData.accepts 1 0 4 leaf00263=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (37303842151/200000000000) (1267232807/2147483648) (-566357093/2147483648) 1 8 ![52,0,4] ![(7/128),0,(1/2)] ![(1/640),1,(1/2)] 34406721456277791125212548300800000000000 24090433103683505733241933650716038004736 129157918941267641722184348467200000000000 raw00263 affine00263
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00263_raw leaf00263_rectangular
    leaf00263_transform leaf00263_sign leaf00263_log
#print axioms leaf00263_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
