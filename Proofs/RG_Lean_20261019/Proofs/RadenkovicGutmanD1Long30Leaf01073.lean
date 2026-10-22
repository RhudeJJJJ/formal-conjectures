/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01073 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5863485805203913244728069455872000000000000 5935908868310963972476480746470563135881216 18674589719551175706556810395648000000000000))
theorem leaf01073_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5863485805203913244728069455872000000000000 5935908868310963972476480746470563135881216 18674589719551175706556810395648000000000000 raw01073=true := by decide +kernel
#print axioms leaf01073_raw
theorem leaf01073_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01073=true := by decide +kernel
#print axioms leaf01073_rectangular
def affine01073 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01073 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf01073_transform : affine01073=(NestedInteger.clearedAll 3 raw01073 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01073_transform
theorem leaf01073_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01073=true := by decide +kernel
#print axioms leaf01073_sign
theorem leaf01073_log : RationalLog.accepts (3299300439/4294967296) (-283181689/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01073_log
def leaf01073 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (317860202417/1000000000000) (3299300439/4294967296) (-283181689/2147483648) 1 8 ![60,0,4] ![(7/20),0,(1/4)] ![(3/160),1,(1/4)] affine01073
theorem leaf01073_checked : FastNestedCellData.accepts 1 2 4 leaf01073=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (317860202417/1000000000000) (3299300439/4294967296) (-283181689/2147483648) 1 8 ![60,0,4] ![(7/20),0,(1/4)] ![(3/160),1,(1/4)] 5863485805203913244728069455872000000000000 5935908868310963972476480746470563135881216 18674589719551175706556810395648000000000000 raw01073 affine01073
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01073_raw leaf01073_rectangular
    leaf01073_transform leaf01073_sign leaf01073_log
#print axioms leaf01073_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
