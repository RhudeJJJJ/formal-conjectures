/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00090 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3837777750658058896897657012224000000000000 256165964044451188465533832888137547776 1231292765276157767145488384000000000000))
theorem leaf00090_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3837777750658058896897657012224000000000000 256165964044451188465533832888137547776 1231292765276157767145488384000000000000 raw00090=true := by decide +kernel
#print axioms leaf00090_raw
theorem leaf00090_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00090=true := by decide +kernel
#print axioms leaf00090_rectangular
def affine00090 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00090 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/3200),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00090_transform : affine00090=(NestedInteger.clearedAll 3 raw00090 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/3200),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00090_transform
theorem leaf00090_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00090=true := by decide +kernel
#print axioms leaf00090_sign
theorem leaf00090_log : RationalLog.accepts (237311/4294967296) (-10526517337/2147483648) 15 8=true := by decide +kernel
#print axioms leaf00090_log
def leaf00090 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (208046348739/1000000000000) (237311/4294967296) (-10526517337/2147483648) 15 8 ![60,0,4] ![(7/3200),0,0] ![(3/32000),1,(1/16)] affine00090
theorem leaf00090_checked : FastNestedCellData.accepts 1 2 4 leaf00090=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (208046348739/1000000000000) (237311/4294967296) (-10526517337/2147483648) 15 8 ![60,0,4] ![(7/3200),0,0] ![(3/32000),1,(1/16)] 3837777750658058896897657012224000000000000 256165964044451188465533832888137547776 1231292765276157767145488384000000000000 raw00090 affine00090
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00090_raw leaf00090_rectangular
    leaf00090_transform leaf00090_sign leaf00090_log
#print axioms leaf00090_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
