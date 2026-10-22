/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00591 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2254504216687206753086879039488000000000000 788991957820455403355379185899330057797632 1613917221179040254167724589056000000000000))
theorem leaf00591_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2254504216687206753086879039488000000000000 788991957820455403355379185899330057797632 1613917221179040254167724589056000000000000 raw00591=true := by decide +kernel
#print axioms leaf00591_raw
theorem leaf00591_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00591=true := by decide +kernel
#print axioms leaf00591_rectangular
def affine00591 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00591 (IntegerComputedClassCell.leftNumerator ![(61/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(61/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(61/3200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00591_transform : affine00591=(NestedInteger.clearedAll 3 raw00591 (IntegerComputedClassCell.leftNumerator ![(61/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(61/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(61/3200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00591_transform
theorem leaf00591_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00591=true := by decide +kernel
#print axioms leaf00591_sign
theorem leaf00591_log : RationalLog.accepts (1009544077/4294967296) (-3109438577/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00591_log
def leaf00591 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (244433836961/500000000000) (1009544077/4294967296) (-3109438577/4294967296) 3 8 ![60,0,4] ![(61/3200),0,(1/16)] ![(1/3200),1,(1/16)] affine00591
theorem leaf00591_checked : FastNestedCellData.accepts 1 2 4 leaf00591=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (244433836961/500000000000) (1009544077/4294967296) (-3109438577/4294967296) 3 8 ![60,0,4] ![(61/3200),0,(1/16)] ![(1/3200),1,(1/16)] 2254504216687206753086879039488000000000000 788991957820455403355379185899330057797632 1613917221179040254167724589056000000000000 raw00591 affine00591
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00591_raw leaf00591_rectangular
    leaf00591_transform leaf00591_sign leaf00591_log
#print axioms leaf00591_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
