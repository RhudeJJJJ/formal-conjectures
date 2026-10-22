/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00085 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 921068625827118429841867669504000000000000 54445797248635270046410012205732855808 272603924282175923429572608000000000000))
theorem leaf00085_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 921068625827118429841867669504000000000000 54445797248635270046410012205732855808 272603924282175923429572608000000000000 raw00085=true := by decide +kernel
#print axioms leaf00085_raw
theorem leaf00085_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00085=true := by decide +kernel
#print axioms leaf00085_rectangular
def affine00085 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00085 (IntegerComputedClassCell.leftNumerator ![(67/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00085_transform : affine00085=(NestedInteger.clearedAll 3 raw00085 (IntegerComputedClassCell.leftNumerator ![(67/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00085_transform
theorem leaf00085_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00085=true := by decide +kernel
#print axioms leaf00085_sign
theorem leaf00085_log : RationalLog.accepts (211617/4294967296) (-21299122299/4294967296) 15 8=true := by decide +kernel
#print axioms leaf00085_log
def leaf00085 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (99862460513/500000000000) (211617/4294967296) (-21299122299/4294967296) 15 8 ![60,0,4] ![(67/32000),0,0] ![(3/32000),1,(1/16)] affine00085
theorem leaf00085_checked : FastNestedCellData.accepts 1 2 4 leaf00085=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (99862460513/500000000000) (211617/4294967296) (-21299122299/4294967296) 15 8 ![60,0,4] ![(67/32000),0,0] ![(3/32000),1,(1/16)] 921068625827118429841867669504000000000000 54445797248635270046410012205732855808 272603924282175923429572608000000000000 raw00085 affine00085
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00085_raw leaf00085_rectangular
    leaf00085_transform leaf00085_sign leaf00085_log
#print axioms leaf00085_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
