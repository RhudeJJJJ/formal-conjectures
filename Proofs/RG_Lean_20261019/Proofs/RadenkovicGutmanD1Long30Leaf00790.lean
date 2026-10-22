/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00790 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 650030706000473876560150423142400000000000 39378803809739993092253710275505394024448 44700086263713380521258831052800000000000))
theorem leaf00790_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 650030706000473876560150423142400000000000 39378803809739993092253710275505394024448 44700086263713380521258831052800000000000 raw00790=true := by decide +kernel
#print axioms leaf00790_raw
theorem leaf00790_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00790=true := by decide +kernel
#print axioms leaf00790_rectangular
def affine00790 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00790 (IntegerComputedClassCell.leftNumerator ![(13/320),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/320),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00790_transform : affine00790=(NestedInteger.clearedAll 3 raw00790 (IntegerComputedClassCell.leftNumerator ![(13/320),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/320),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00790_transform
theorem leaf00790_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00790=true := by decide +kernel
#print axioms leaf00790_sign
theorem leaf00790_log : RationalLog.accepts (138327937/4294967296) (-3688917433/2147483648) 5 8=true := by decide +kernel
#print axioms leaf00790_log
def leaf00790 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (176191175907/200000000000) (138327937/4294967296) (-3688917433/2147483648) 5 8 ![60,0,4] ![(13/320),0,0] ![(3/3200),1,(1/16)] affine00790
theorem leaf00790_checked : FastNestedCellData.accepts 1 2 4 leaf00790=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (176191175907/200000000000) (138327937/4294967296) (-3688917433/2147483648) 5 8 ![60,0,4] ![(13/320),0,0] ![(3/3200),1,(1/16)] 650030706000473876560150423142400000000000 39378803809739993092253710275505394024448 44700086263713380521258831052800000000000 raw00790 affine00790
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00790_raw leaf00790_rectangular
    leaf00790_transform leaf00790_sign leaf00790_log
#print axioms leaf00790_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
