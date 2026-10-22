/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00602 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 770420679784394809267768524800000000000 423547303570078077472983229300071202816 1491367928068306541425878630400000000000))
theorem leaf00602_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 770420679784394809267768524800000000000 423547303570078077472983229300071202816 1491367928068306541425878630400000000000 raw00602=true := by decide +kernel
#print axioms leaf00602_raw
theorem leaf00602_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00602=true := by decide +kernel
#print axioms leaf00602_rectangular
def affine00602 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00602 (IntegerComputedClassCell.leftNumerator ![(63/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(63/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(63/3200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00602_transform : affine00602=(NestedInteger.clearedAll 3 raw00602 (IntegerComputedClassCell.leftNumerator ![(63/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(63/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(63/3200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00602_transform
theorem leaf00602_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00602=true := by decide +kernel
#print axioms leaf00602_sign
theorem leaf00602_log : RationalLog.accepts (459736627/1073741824) (-910802701/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00602_log
def leaf00602 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (56799840683/200000000000) (459736627/1073741824) (-910802701/2147483648) 2 8 ![60,0,4] ![(63/3200),0,(1/8)] ![(1/3200),1,(1/8)] affine00602
theorem leaf00602_checked : FastNestedCellData.accepts 1 2 4 leaf00602=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (56799840683/200000000000) (459736627/1073741824) (-910802701/2147483648) 2 8 ![60,0,4] ![(63/3200),0,(1/8)] ![(1/3200),1,(1/8)] 770420679784394809267768524800000000000 423547303570078077472983229300071202816 1491367928068306541425878630400000000000 raw00602 affine00602
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00602_raw leaf00602_rectangular
    leaf00602_transform leaf00602_sign leaf00602_log
#print axioms leaf00602_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
