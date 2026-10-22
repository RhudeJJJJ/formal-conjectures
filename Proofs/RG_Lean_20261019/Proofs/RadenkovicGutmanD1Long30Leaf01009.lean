/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01009 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8121125723837470279431356416000000000000 5777775629869200253213138611191339286528 17088460595937301094933200896000000000000))
theorem leaf01009_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8121125723837470279431356416000000000000 5777775629869200253213138611191339286528 17088460595937301094933200896000000000000 raw01009=true := by decide +kernel
#print axioms leaf01009_raw
theorem leaf01009_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01009=true := by decide +kernel
#print axioms leaf01009_rectangular
def affine01009 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01009 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf01009_transform : affine01009=(NestedInteger.clearedAll 3 raw01009 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01009_transform
theorem leaf01009_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01009=true := by decide +kernel
#print axioms leaf01009_sign
theorem leaf01009_log : RationalLog.accepts (570890169/1073741824) (-1356582671/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01009_log
def leaf01009 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (84527444667/250000000000) (570890169/1073741824) (-1356582671/4294967296) 1 8 ![60,0,4] ![(5/32),0,(1/2)] ![(1/160),1,(1/2)] affine01009
theorem leaf01009_checked : FastNestedCellData.accepts 1 2 4 leaf01009=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (84527444667/250000000000) (570890169/1073741824) (-1356582671/4294967296) 1 8 ![60,0,4] ![(5/32),0,(1/2)] ![(1/160),1,(1/2)] 8121125723837470279431356416000000000000 5777775629869200253213138611191339286528 17088460595937301094933200896000000000000 raw01009 affine01009
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01009_raw leaf01009_rectangular
    leaf01009_transform leaf01009_sign leaf01009_log
#print axioms leaf01009_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
