/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00023 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 178144905923975457852218146816000000000000 173865154184891796845182753836356446715904 18003579647421768548546305327104000000000000))
theorem leaf00023_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 178144905923975457852218146816000000000000 173865154184891796845182753836356446715904 18003579647421768548546305327104000000000000 raw00023=true := by decide +kernel
#print axioms leaf00023_raw
theorem leaf00023_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00023=true := by decide +kernel
#print axioms leaf00023_rectangular
def affine00023 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00023 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/2)] ![(3/16000),1,(1/2)]))
theorem leaf00023_transform : affine00023=(NestedInteger.clearedAll 3 raw00023 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/2)] ![(3/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00023_transform
theorem leaf00023_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00023=true := by decide +kernel
#print axioms leaf00023_sign
theorem leaf00023_log : RationalLog.accepts (4151691099/4294967296) (-72860283/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00023_log
def leaf00023 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (9657254701/1000000000000) (4151691099/4294967296) (-72860283/4294967296) 1 8 ![52,0,4] ![(41/16000),0,(1/2)] ![(3/16000),1,(1/2)] affine00023
theorem leaf00023_checked : FastNestedCellData.accepts 1 0 4 leaf00023=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (9657254701/1000000000000) (4151691099/4294967296) (-72860283/4294967296) 1 8 ![52,0,4] ![(41/16000),0,(1/2)] ![(3/16000),1,(1/2)] 178144905923975457852218146816000000000000 173865154184891796845182753836356446715904 18003579647421768548546305327104000000000000 raw00023 affine00023
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00023_raw leaf00023_rectangular
    leaf00023_transform leaf00023_sign leaf00023_log
#print axioms leaf00023_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
