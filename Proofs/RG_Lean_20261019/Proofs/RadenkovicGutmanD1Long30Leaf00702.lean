/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00702 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 70740555703161925174563920936960000000000 32622267837588236514487510454662084952064 85067839787565974263739449344000000000000))
theorem leaf00702_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 70740555703161925174563920936960000000000 32622267837588236514487510454662084952064 85067839787565974263739449344000000000000 raw00702=true := by decide +kernel
#print axioms leaf00702_raw
theorem leaf00702_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00702=true := by decide +kernel
#print axioms leaf00702_rectangular
def affine00702 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00702 (IntegerComputedClassCell.leftNumerator ![(37/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/1280),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00702_transform : affine00702=(NestedInteger.clearedAll 3 raw00702 (IntegerComputedClassCell.leftNumerator ![(37/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/1280),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00702_transform
theorem leaf00702_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00702=true := by decide +kernel
#print axioms leaf00702_sign
theorem leaf00702_log : RationalLog.accepts (715815325/2147483648) (-1179644835/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00702_log
def leaf00702 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (383485320881/1000000000000) (715815325/2147483648) (-1179644835/2147483648) 2 8 ![60,0,4] ![(37/1280),0,(1/8)] ![(3/6400),1,(1/8)] affine00702
theorem leaf00702_checked : FastNestedCellData.accepts 1 2 4 leaf00702=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (383485320881/1000000000000) (715815325/2147483648) (-1179644835/2147483648) 2 8 ![60,0,4] ![(37/1280),0,(1/8)] ![(3/6400),1,(1/8)] 70740555703161925174563920936960000000000 32622267837588236514487510454662084952064 85067839787565974263739449344000000000000 raw00702 affine00702
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00702_raw leaf00702_rectangular
    leaf00702_transform leaf00702_sign leaf00702_log
#print axioms leaf00702_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
