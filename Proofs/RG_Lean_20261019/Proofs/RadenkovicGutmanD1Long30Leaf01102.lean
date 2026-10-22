/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01102 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 20069651655804001776268476416000000000000 23252057748539286978155803934127311290368 111311504323405398396951855104000000000000))
theorem leaf01102_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 20069651655804001776268476416000000000000 23252057748539286978155803934127311290368 111311504323405398396951855104000000000000 raw01102=true := by decide +kernel
#print axioms leaf01102_raw
theorem leaf01102_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01102=true := by decide +kernel
#print axioms leaf01102_rectangular
def affine01102 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01102 (IntegerComputedClassCell.leftNumerator ![(17/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/32),0,(3/4)] ![(1/32),1,(1/8)]))
theorem leaf01102_transform : affine01102=(NestedInteger.clearedAll 3 raw01102 (IntegerComputedClassCell.leftNumerator ![(17/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/32),0,(3/4)] ![(1/32),1,(1/8)])) := by decide +kernel
#print axioms leaf01102_transform
theorem leaf01102_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01102=true := by decide +kernel
#print axioms leaf01102_sign
theorem leaf01102_log : RationalLog.accepts (2058088287/2147483648) (-1426709/67108864) 1 8=true := by decide +kernel
#print axioms leaf01102_log
def leaf01102 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (52222943823/250000000000) (2058088287/2147483648) (-1426709/67108864) 1 8 ![60,0,4] ![(17/32),0,(3/4)] ![(1/32),1,(1/8)] affine01102
theorem leaf01102_checked : FastNestedCellData.accepts 1 2 4 leaf01102=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (52222943823/250000000000) (2058088287/2147483648) (-1426709/67108864) 1 8 ![60,0,4] ![(17/32),0,(3/4)] ![(1/32),1,(1/8)] 20069651655804001776268476416000000000000 23252057748539286978155803934127311290368 111311504323405398396951855104000000000000 raw01102 affine01102
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01102_raw leaf01102_rectangular
    leaf01102_transform leaf01102_sign leaf01102_log
#print axioms leaf01102_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
