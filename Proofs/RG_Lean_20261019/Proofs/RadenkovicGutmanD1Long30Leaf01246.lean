/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01246 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 636806385858105139510483353600000000000 686220993443362550312052860184642453504 141986899956355458222434287616000000000000))
theorem leaf01246_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 636806385858105139510483353600000000000 686220993443362550312052860184642453504 141986899956355458222434287616000000000000 raw01246=true := by decide +kernel
#print axioms leaf01246_raw
theorem leaf01246_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01246=true := by decide +kernel
#print axioms leaf01246_rectangular
def affine01246 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01246 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf01246_transform : affine01246=(NestedInteger.clearedAll 3 raw01246 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf01246_transform
theorem leaf01246_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01246=true := by decide +kernel
#print axioms leaf01246_sign
theorem leaf01246_log : RationalLog.accepts (2302992755/2147483648) (150136411/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01246_log
def leaf01246 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4832988069/1000000000000) (2302992755/2147483648) (150136411/4294967296) 0 8 ![60,0,4] ![(7/32),0,(1/2)] ![(1/64),1,(1/4)] affine01246
theorem leaf01246_checked : FastNestedCellData.accepts 1 2 4 leaf01246=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4832988069/1000000000000) (2302992755/2147483648) (150136411/4294967296) 0 8 ![60,0,4] ![(7/32),0,(1/2)] ![(1/64),1,(1/4)] 636806385858105139510483353600000000000 686220993443362550312052860184642453504 141986899956355458222434287616000000000000 raw01246 affine01246
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01246_raw leaf01246_rectangular
    leaf01246_transform leaf01246_sign leaf01246_log
#print axioms leaf01246_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
