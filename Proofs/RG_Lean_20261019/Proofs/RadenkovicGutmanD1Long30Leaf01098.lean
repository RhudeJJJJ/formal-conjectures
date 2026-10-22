/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01098 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4024368094722975196118561849344000000000000 4575688274218800490805871549406331386462208 20973864360535892860302641856512000000000000))
theorem leaf01098_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4024368094722975196118561849344000000000000 4575688274218800490805871549406331386462208 20973864360535892860302641856512000000000000 raw01098=true := by decide +kernel
#print axioms leaf01098_raw
theorem leaf01098_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01098=true := by decide +kernel
#print axioms leaf01098_rectangular
def affine01098 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01098 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/2),0,(7/8)] ![(1/32),1,(1/16)]))
theorem leaf01098_transform : affine01098=(NestedInteger.clearedAll 3 raw01098 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/2),0,(7/8)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01098_transform
theorem leaf01098_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01098=true := by decide +kernel
#print axioms leaf01098_sign
theorem leaf01098_log : RationalLog.accepts (4008794083/4294967296) (-74038245/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01098_log
def leaf01098 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (218161431559/1000000000000) (4008794083/4294967296) (-74038245/2147483648) 1 8 ![60,0,4] ![(1/2),0,(7/8)] ![(1/32),1,(1/16)] affine01098
theorem leaf01098_checked : FastNestedCellData.accepts 1 2 4 leaf01098=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (218161431559/1000000000000) (4008794083/4294967296) (-74038245/2147483648) 1 8 ![60,0,4] ![(1/2),0,(7/8)] ![(1/32),1,(1/16)] 4024368094722975196118561849344000000000000 4575688274218800490805871549406331386462208 20973864360535892860302641856512000000000000 raw01098 affine01098
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01098_raw leaf01098_rectangular
    leaf01098_transform leaf01098_sign leaf01098_log
#print axioms leaf01098_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
