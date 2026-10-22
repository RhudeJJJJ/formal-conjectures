/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00786 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 126018178002522592081871267430400000000000 31677773282659568498773163404556415008768 46370435268356109292532871987200000000000))
theorem leaf00786_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 126018178002522592081871267430400000000000 31677773282659568498773163404556415008768 46370435268356109292532871987200000000000 raw00786=true := by decide +kernel
#print axioms leaf00786_raw
theorem leaf00786_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00786=true := by decide +kernel
#print axioms leaf00786_rectangular
def affine00786 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00786 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00786_transform : affine00786=(NestedInteger.clearedAll 3 raw00786 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00786_transform
theorem leaf00786_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00786=true := by decide +kernel
#print axioms leaf00786_sign
theorem leaf00786_log : RationalLog.accepts (320722589/2147483648) (-4083387647/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00786_log
def leaf00786 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (136629182363/200000000000) (320722589/2147483648) (-4083387647/4294967296) 3 8 ![60,0,4] ![(127/3200),0,(1/16)] ![(3/3200),1,(1/16)] affine00786
theorem leaf00786_checked : FastNestedCellData.accepts 1 2 4 leaf00786=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (136629182363/200000000000) (320722589/2147483648) (-4083387647/4294967296) 3 8 ![60,0,4] ![(127/3200),0,(1/16)] ![(3/3200),1,(1/16)] 126018178002522592081871267430400000000000 31677773282659568498773163404556415008768 46370435268356109292532871987200000000000 raw00786 affine00786
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00786_raw leaf00786_rectangular
    leaf00786_transform leaf00786_sign leaf00786_log
#print axioms leaf00786_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
