/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01196 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 344454125491980655026287673344000000000000 402824525751920765120003794581852140863488 21572686704058952698606682898432000000000000))
theorem leaf01196_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 344454125491980655026287673344000000000000 402824525751920765120003794581852140863488 21572686704058952698606682898432000000000000 raw01196=true := by decide +kernel
#print axioms leaf01196_raw
theorem leaf01196_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01196=true := by decide +kernel
#print axioms leaf01196_rectangular
def affine01196 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01196 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf01196_transform : affine01196=(NestedInteger.clearedAll 3 raw01196 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf01196_transform
theorem leaf01196_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01196=true := by decide +kernel
#print axioms leaf01196_sign
theorem leaf01196_log : RationalLog.accepts (4930711863/4294967296) (74109355/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01196_log
def leaf01196 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (18672895559/1000000000000) (4930711863/4294967296) (74109355/1073741824) 0 8 ![60,0,4] ![(3/8),0,(1/2)] ![(1/32),1,(1/4)] affine01196
theorem leaf01196_checked : FastNestedCellData.accepts 1 2 4 leaf01196=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (18672895559/1000000000000) (4930711863/4294967296) (74109355/1073741824) 0 8 ![60,0,4] ![(3/8),0,(1/2)] ![(1/32),1,(1/4)] 344454125491980655026287673344000000000000 402824525751920765120003794581852140863488 21572686704058952698606682898432000000000000 raw01196 affine01196
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01196_raw leaf01196_rectangular
    leaf01196_transform leaf01196_sign leaf01196_log
#print axioms leaf01196_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
