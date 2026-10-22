/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00785 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 253959066409089196329330016256000000000000 14705984307435495374602516211960830230528 16690529889511357295961833472000000000000))
theorem leaf00785_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 253959066409089196329330016256000000000000 14705984307435495374602516211960830230528 16690529889511357295961833472000000000000 raw00785=true := by decide +kernel
#print axioms leaf00785_raw
theorem leaf00785_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00785=true := by decide +kernel
#print axioms leaf00785_rectangular
def affine00785 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00785 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(127/3200),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00785_transform : affine00785=(NestedInteger.clearedAll 3 raw00785 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(127/3200),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00785_transform
theorem leaf00785_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00785=true := by decide +kernel
#print axioms leaf00785_sign
theorem leaf00785_log : RationalLog.accepts (33053613/1073741824) (-934363177/536870912) 6 8=true := by decide +kernel
#print axioms leaf00785_log
def leaf00785 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (440548754437/500000000000) (33053613/1073741824) (-934363177/536870912) 6 8 ![60,0,4] ![(127/3200),0,0] ![(3/3200),1,(1/16)] affine00785
theorem leaf00785_checked : FastNestedCellData.accepts 1 2 4 leaf00785=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (440548754437/500000000000) (33053613/1073741824) (-934363177/536870912) 6 8 ![60,0,4] ![(127/3200),0,0] ![(3/3200),1,(1/16)] 253959066409089196329330016256000000000000 14705984307435495374602516211960830230528 16690529889511357295961833472000000000000 raw00785 affine00785
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00785_raw leaf00785_rectangular
    leaf00785_transform leaf00785_sign leaf00785_log
#print axioms leaf00785_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
