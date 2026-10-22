/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00808 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1071466234461480485098753517158400000000000 615890778728249827468128058877007517188096 2120678973755591717900053905408000000000000))
theorem leaf00808_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1071466234461480485098753517158400000000000 615890778728249827468128058877007517188096 2120678973755591717900053905408000000000000 raw00808=true := by decide +kernel
#print axioms leaf00808_raw
theorem leaf00808_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00808=true := by decide +kernel
#print axioms leaf00808_rectangular
def affine00808 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00808 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00808_transform : affine00808=(NestedInteger.clearedAll 3 raw00808 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00808_transform
theorem leaf00808_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00808=true := by decide +kernel
#print axioms leaf00808_sign
theorem leaf00808_log : RationalLog.accepts (1913169645/4294967296) (-434158169/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00808_log
def leaf00808 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (290421504787/1000000000000) (1913169645/4294967296) (-434158169/1073741824) 2 8 ![60,0,4] ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00808
theorem leaf00808_checked : FastNestedCellData.accepts 1 2 4 leaf00808=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (290421504787/1000000000000) (1913169645/4294967296) (-434158169/1073741824) 2 8 ![60,0,4] ![(139/3200),0,(1/4)] ![(3/3200),1,(1/4)] 1071466234461480485098753517158400000000000 615890778728249827468128058877007517188096 2120678973755591717900053905408000000000000 raw00808 affine00808
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00808_raw leaf00808_rectangular
    leaf00808_transform leaf00808_sign leaf00808_log
#print axioms leaf00808_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
