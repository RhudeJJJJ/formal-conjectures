/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00224 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12719406902114812910629604556800000000000 12214288196112901881312532768615670218752 708567152950391195577163028889600000000000))
theorem leaf00224_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12719406902114812910629604556800000000000 12214288196112901881312532768615670218752 708567152950391195577163028889600000000000 raw00224=true := by decide +kernel
#print axioms leaf00224_raw
theorem leaf00224_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00224=true := by decide +kernel
#print axioms leaf00224_rectangular
def affine00224 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00224 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00224_transform : affine00224=(NestedInteger.clearedAll 3 raw00224 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00224_transform
theorem leaf00224_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00224=true := by decide +kernel
#print axioms leaf00224_sign
theorem leaf00224_log : RationalLog.accepts (4054511937/4294967296) (-61862173/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00224_log
def leaf00224 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3447602149/200000000000) (4054511937/4294967296) (-61862173/2147483648) 1 8 ![60,0,4] ![(37/8000),0,(1/2)] ![(3/32000),1,(1/2)] affine00224
theorem leaf00224_checked : FastNestedCellData.accepts 1 2 4 leaf00224=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3447602149/200000000000) (4054511937/4294967296) (-61862173/2147483648) 1 8 ![60,0,4] ![(37/8000),0,(1/2)] ![(3/32000),1,(1/2)] 12719406902114812910629604556800000000000 12214288196112901881312532768615670218752 708567152950391195577163028889600000000000 raw00224 affine00224
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00224_raw leaf00224_rectangular
    leaf00224_transform leaf00224_sign leaf00224_log
#print axioms leaf00224_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
