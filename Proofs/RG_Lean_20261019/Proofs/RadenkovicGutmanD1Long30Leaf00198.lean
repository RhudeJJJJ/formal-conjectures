/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00198 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9216864535136876114416238592000000000000 8556562588927998237281058013181626023936 267581371535884887934319460352000000000000))
theorem leaf00198_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9216864535136876114416238592000000000000 8556562588927998237281058013181626023936 267581371535884887934319460352000000000000 raw00198=true := by decide +kernel
#print axioms leaf00198_raw
theorem leaf00198_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00198=true := by decide +kernel
#print axioms leaf00198_rectangular
def affine00198 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00198 (IntegerComputedClassCell.leftNumerator ![(133/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(133/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(133/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00198_transform : affine00198=(NestedInteger.clearedAll 3 raw00198 (IntegerComputedClassCell.leftNumerator ![(133/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(133/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(133/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00198_transform
theorem leaf00198_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00198=true := by decide +kernel
#print axioms leaf00198_sign
theorem leaf00198_log : RationalLog.accepts (3863721301/4294967296) (-113616027/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00198_log
def leaf00198 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3997177821/125000000000) (3863721301/4294967296) (-113616027/2147483648) 1 8 ![60,0,4] ![(133/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00198
theorem leaf00198_checked : FastNestedCellData.accepts 1 2 4 leaf00198=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3997177821/125000000000) (3863721301/4294967296) (-113616027/2147483648) 1 8 ![60,0,4] ![(133/32000),0,(1/4)] ![(3/32000),1,(1/4)] 9216864535136876114416238592000000000000 8556562588927998237281058013181626023936 267581371535884887934319460352000000000000 raw00198 affine00198
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00198_raw leaf00198_rectangular
    leaf00198_transform leaf00198_sign leaf00198_log
#print axioms leaf00198_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
