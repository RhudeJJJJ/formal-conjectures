/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00081 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2898392235637919122435604480000000000 2493629526147575343627015828472332288 38746684684954525212082176000000000000))
theorem leaf00081_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2898392235637919122435604480000000000 2493629526147575343627015828472332288 38746684684954525212082176000000000000 raw00081=true := by decide +kernel
#print axioms leaf00081_raw
theorem leaf00081_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00081=true := by decide +kernel
#print axioms leaf00081_rectangular
def affine00081 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00081 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00081_transform : affine00081=(NestedInteger.clearedAll 3 raw00081 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00081_transform
theorem leaf00081_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00081=true := by decide +kernel
#print axioms leaf00081_sign
theorem leaf00081_log : RationalLog.accepts (433967525/536870912) (-456958731/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00081_log
def leaf00081 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4022327243/62500000000) (433967525/536870912) (-456958731/4294967296) 1 8 ![60,0,4] ![(1/500),0,(1/16)] ![(3/32000),1,(1/16)] affine00081
theorem leaf00081_checked : FastNestedCellData.accepts 1 2 4 leaf00081=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4022327243/62500000000) (433967525/536870912) (-456958731/4294967296) 1 8 ![60,0,4] ![(1/500),0,(1/16)] ![(3/32000),1,(1/16)] 2898392235637919122435604480000000000 2493629526147575343627015828472332288 38746684684954525212082176000000000000 raw00081 affine00081
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00081_raw leaf00081_rectangular
    leaf00081_transform leaf00081_sign leaf00081_log
#print axioms leaf00081_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
