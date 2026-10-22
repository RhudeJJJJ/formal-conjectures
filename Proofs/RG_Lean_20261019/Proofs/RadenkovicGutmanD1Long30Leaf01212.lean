/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01212 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 242374478680094468497863606272000000000000 276915309742149222624041422717142597369856 21075592928443735999699608403968000000000000))
theorem leaf01212_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 242374478680094468497863606272000000000000 276915309742149222624041422717142597369856 21075592928443735999699608403968000000000000 raw01212=true := by decide +kernel
#print axioms leaf01212_raw
theorem leaf01212_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01212=true := by decide +kernel
#print axioms leaf01212_rectangular
def affine01212 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01212 (IntegerComputedClassCell.leftNumerator ![(21/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/64),0,(3/4)] ![(1/64),1,(1/8)]))
theorem leaf01212_transform : affine01212=(NestedInteger.clearedAll 3 raw01212 (IntegerComputedClassCell.leftNumerator ![(21/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/64),0,(3/4)] ![(1/64),1,(1/8)])) := by decide +kernel
#print axioms leaf01212_transform
theorem leaf01212_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01212=true := by decide +kernel
#print axioms leaf01212_sign
theorem leaf01212_log : RationalLog.accepts (4843405649/4294967296) (258072083/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01212_log
def leaf01212 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (13139146817/1000000000000) (4843405649/4294967296) (258072083/4294967296) 0 8 ![60,0,4] ![(21/64),0,(3/4)] ![(1/64),1,(1/8)] affine01212
theorem leaf01212_checked : FastNestedCellData.accepts 1 2 4 leaf01212=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (13139146817/1000000000000) (4843405649/4294967296) (258072083/4294967296) 0 8 ![60,0,4] ![(21/64),0,(3/4)] ![(1/64),1,(1/8)] 242374478680094468497863606272000000000000 276915309742149222624041422717142597369856 21075592928443735999699608403968000000000000 raw01212 affine01212
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01212_raw leaf01212_rectangular
    leaf01212_transform leaf01212_sign leaf01212_log
#print axioms leaf01212_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
