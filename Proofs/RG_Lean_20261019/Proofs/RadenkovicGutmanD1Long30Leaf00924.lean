/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00924 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11347676386494688555812226334720000000000 7542491029864335219456222951554565537792 30652619304456603670249734144000000000000))
theorem leaf00924_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11347676386494688555812226334720000000000 7542491029864335219456222951554565537792 30652619304456603670249734144000000000000 raw00924=true := by decide +kernel
#print axioms leaf00924_raw
theorem leaf00924_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00924=true := by decide +kernel
#print axioms leaf00924_rectangular
def affine00924 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00924 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00924_transform : affine00924=(NestedInteger.clearedAll 3 raw00924 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00924_transform
theorem leaf00924_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00924=true := by decide +kernel
#print axioms leaf00924_sign
theorem leaf00924_log : RationalLog.accepts (1145506475/2147483648) (-1349585887/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00924_log
def leaf00924 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (123031753909/500000000000) (1145506475/2147483648) (-1349585887/4294967296) 1 8 ![60,0,4] ![(5/64),0,(1/2)] ![(1/320),1,(1/2)] affine00924
theorem leaf00924_checked : FastNestedCellData.accepts 1 2 4 leaf00924=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (123031753909/500000000000) (1145506475/2147483648) (-1349585887/4294967296) 1 8 ![60,0,4] ![(5/64),0,(1/2)] ![(1/320),1,(1/2)] 11347676386494688555812226334720000000000 7542491029864335219456222951554565537792 30652619304456603670249734144000000000000 raw00924 affine00924
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00924_raw leaf00924_rectangular
    leaf00924_transform leaf00924_sign leaf00924_log
#print axioms leaf00924_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
