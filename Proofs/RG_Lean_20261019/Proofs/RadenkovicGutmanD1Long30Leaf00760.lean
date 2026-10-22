/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00760 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 202933100854113654854812644147200000000000 9197337749973497871843746008973594066944 10450545950805489829915131904000000000000))
theorem leaf00760_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 202933100854113654854812644147200000000000 9197337749973497871843746008973594066944 10450545950805489829915131904000000000000 raw00760=true := by decide +kernel
#print axioms leaf00760_raw
theorem leaf00760_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00760=true := by decide +kernel
#print axioms leaf00760_rectangular
def affine00760 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00760 (IntegerComputedClassCell.leftNumerator ![(7/200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/200),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00760_transform : affine00760=(NestedInteger.clearedAll 3 raw00760 (IntegerComputedClassCell.leftNumerator ![(7/200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/200),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00760_transform
theorem leaf00760_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00760=true := by decide +kernel
#print axioms leaf00760_sign
theorem leaf00760_log : RationalLog.accepts (25884055/1073741824) (-7999973193/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00760_log
def leaf00760 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (880082035261/1000000000000) (25884055/1073741824) (-7999973193/4294967296) 6 8 ![60,0,4] ![(7/200),0,0] ![(3/3200),1,(1/16)] affine00760
theorem leaf00760_checked : FastNestedCellData.accepts 1 2 4 leaf00760=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (880082035261/1000000000000) (25884055/1073741824) (-7999973193/4294967296) 6 8 ![60,0,4] ![(7/200),0,0] ![(3/3200),1,(1/16)] 202933100854113654854812644147200000000000 9197337749973497871843746008973594066944 10450545950805489829915131904000000000000 raw00760 affine00760
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00760_raw leaf00760_rectangular
    leaf00760_transform leaf00760_sign leaf00760_log
#print axioms leaf00760_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
