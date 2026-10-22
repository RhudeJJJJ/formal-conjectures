/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00158 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1403285913154118332630935011328000000000000 1183469629229206617249573109541581048774656 15557172750583623929228513247232000000000000))
theorem leaf00158_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1403285913154118332630935011328000000000000 1183469629229206617249573109541581048774656 15557172750583623929228513247232000000000000 raw00158=true := by decide +kernel
#print axioms leaf00158_raw
theorem leaf00158_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00158=true := by decide +kernel
#print axioms leaf00158_rectangular
def affine00158 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00158 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00158_transform : affine00158=(NestedInteger.clearedAll 3 raw00158 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00158_transform
theorem leaf00158_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00158=true := by decide +kernel
#print axioms leaf00158_sign
theorem leaf00158_log : RationalLog.accepts (3366118249/4294967296) (-261653415/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00158_log
def leaf00158 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (76072281783/1000000000000) (3366118249/4294967296) (-261653415/2147483648) 1 8 ![52,0,4] ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)] affine00158
theorem leaf00158_checked : FastNestedCellData.accepts 1 0 4 leaf00158=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (76072281783/1000000000000) (3366118249/4294967296) (-261653415/2147483648) 1 8 ![52,0,4] ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)] 1403285913154118332630935011328000000000000 1183469629229206617249573109541581048774656 15557172750583623929228513247232000000000000 raw00158 affine00158
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00158_raw leaf00158_rectangular
    leaf00158_transform leaf00158_sign leaf00158_log
#print axioms leaf00158_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
