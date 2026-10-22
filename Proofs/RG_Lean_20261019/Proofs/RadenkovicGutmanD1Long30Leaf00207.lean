/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00207 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 76617076582400558706458624000000000000 65588100987486923970252867942507085824 963827387911051756462669824000000000000))
theorem leaf00207_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 76617076582400558706458624000000000000 65588100987486923970252867942507085824 963827387911051756462669824000000000000 raw00207=true := by decide +kernel
#print axioms leaf00207_raw
theorem leaf00207_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00207=true := by decide +kernel
#print axioms leaf00207_rectangular
def affine00207 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00207 (IntegerComputedClassCell.leftNumerator ![(139/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(139/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(139/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00207_transform : affine00207=(NestedInteger.clearedAll 3 raw00207 (IntegerComputedClassCell.leftNumerator ![(139/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(139/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(139/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00207_transform
theorem leaf00207_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00207=true := by decide +kernel
#print axioms leaf00207_sign
theorem leaf00207_log : RationalLog.accepts (26894157/33554432) (-7424251/67108864) 1 8=true := by decide +kernel
#print axioms leaf00207_log
def leaf00207 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (68049634001/1000000000000) (26894157/33554432) (-7424251/67108864) 1 8 ![60,0,4] ![(139/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00207
theorem leaf00207_checked : FastNestedCellData.accepts 1 2 4 leaf00207=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (68049634001/1000000000000) (26894157/33554432) (-7424251/67108864) 1 8 ![60,0,4] ![(139/32000),0,(1/8)] ![(3/32000),1,(1/8)] 76617076582400558706458624000000000000 65588100987486923970252867942507085824 963827387911051756462669824000000000000 raw00207 affine00207
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00207_raw leaf00207_rectangular
    leaf00207_transform leaf00207_sign leaf00207_log
#print axioms leaf00207_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
