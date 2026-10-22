/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00961 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 32205087868809662412383804456960000000000 12689829491860432481731128794529348452352 18171510502387989326591950848000000000000))
theorem leaf00961_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 32205087868809662412383804456960000000000 12689829491860432481731128794529348452352 18171510502387989326591950848000000000000 raw00961=true := by decide +kernel
#print axioms leaf00961_raw
theorem leaf00961_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00961=true := by decide +kernel
#print axioms leaf00961_rectangular
def affine00961 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00961 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00961_transform : affine00961=(NestedInteger.clearedAll 3 raw00961 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00961_transform
theorem leaf00961_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00961=true := by decide +kernel
#print axioms leaf00961_sign
theorem leaf00961_log : RationalLog.accepts (249119325/1073741824) (-1568707717/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00961_log
def leaf00961 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (698336524649/1000000000000) (249119325/1073741824) (-1568707717/2147483648) 3 8 ![60,0,4] ![(33/320),0,(1/16)] ![(1/320),1,(1/16)] affine00961
theorem leaf00961_checked : FastNestedCellData.accepts 1 2 4 leaf00961=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (698336524649/1000000000000) (249119325/1073741824) (-1568707717/2147483648) 3 8 ![60,0,4] ![(33/320),0,(1/16)] ![(1/320),1,(1/16)] 32205087868809662412383804456960000000000 12689829491860432481731128794529348452352 18171510502387989326591950848000000000000 raw00961 affine00961
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00961_raw leaf00961_rectangular
    leaf00961_transform leaf00961_sign leaf00961_log
#print axioms leaf00961_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
