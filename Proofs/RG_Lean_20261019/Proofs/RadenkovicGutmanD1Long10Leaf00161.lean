/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00161 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 358398319143005763057309712384000000000000 301271903557288529981021833762502971752448 3876612559741872020100783013888000000000000))
theorem leaf00161_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 358398319143005763057309712384000000000000 301271903557288529981021833762502971752448 3876612559741872020100783013888000000000000 raw00161=true := by decide +kernel
#print axioms leaf00161_raw
theorem leaf00161_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00161=true := by decide +kernel
#print axioms leaf00161_rectangular
def affine00161 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00161 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00161_transform : affine00161=(NestedInteger.clearedAll 3 raw00161 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00161_transform
theorem leaf00161_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00161=true := by decide +kernel
#print axioms leaf00161_sign
theorem leaf00161_log : RationalLog.accepts (3350028497/4294967296) (-533596225/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00161_log
def leaf00161 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (38857623623/500000000000) (3350028497/4294967296) (-533596225/4294967296) 1 8 ![52,0,4] ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00161
theorem leaf00161_checked : FastNestedCellData.accepts 1 0 4 leaf00161=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (38857623623/500000000000) (3350028497/4294967296) (-533596225/4294967296) 1 8 ![52,0,4] ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)] 358398319143005763057309712384000000000000 301271903557288529981021833762502971752448 3876612559741872020100783013888000000000000 raw00161 affine00161
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00161_raw leaf00161_rectangular
    leaf00161_transform leaf00161_sign leaf00161_log
#print axioms leaf00161_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
