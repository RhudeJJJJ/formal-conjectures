/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01153 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 413727272914127287443194380288000000000000 530039610301455706667109422786066899795968 5908182563897053575700329529344000000000000))
theorem leaf01153_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 413727272914127287443194380288000000000000 530039610301455706667109422786066899795968 5908182563897053575700329529344000000000000 raw01153=true := by decide +kernel
#print axioms leaf01153_raw
theorem leaf01153_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01153=true := by decide +kernel
#print axioms leaf01153_rectangular
def affine01153 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01153 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01153_transform : affine01153=(NestedInteger.clearedAll 3 raw01153 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01153_transform
theorem leaf01153_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01153=true := by decide +kernel
#print axioms leaf01153_sign
theorem leaf01153_log : RationalLog.accepts (5049425673/4294967296) (347528497/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01153_log
def leaf01153 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (44856400811/500000000000) (5049425673/4294967296) (347528497/4294967296) 0 8 ![60,0,4] ![(7/8),0,(7/8)] ![(1/16),1,(1/16)] affine01153
theorem leaf01153_checked : FastNestedCellData.accepts 1 2 4 leaf01153=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (44856400811/500000000000) (5049425673/4294967296) (347528497/4294967296) 0 8 ![60,0,4] ![(7/8),0,(7/8)] ![(1/16),1,(1/16)] 413727272914127287443194380288000000000000 530039610301455706667109422786066899795968 5908182563897053575700329529344000000000000 raw01153 affine01153
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01153_raw leaf01153_rectangular
    leaf01153_transform leaf01153_sign leaf01153_log
#print axioms leaf01153_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
