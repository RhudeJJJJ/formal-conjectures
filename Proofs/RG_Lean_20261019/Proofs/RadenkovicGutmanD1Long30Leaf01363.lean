/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01363 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 3355001578405924700160000000000 3355027168198554718117577097216 461172119340007521390732247040000000000))
theorem leaf01363_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 3355001578405924700160000000000 3355027168198554718117577097216 461172119340007521390732247040000000000 raw01363=true := by decide +kernel
#print axioms leaf01363_raw
theorem leaf01363_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01363=true := by decide +kernel
#print axioms leaf01363_rectangular
def affine01363 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01363 (IntegerComputedClassCell.leftNumerator ![(1/512),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/512),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/512),0,0] ![(1/1024),1,1]))
theorem leaf01363_transform : affine01363=(NestedInteger.clearedAll 3 raw01363 (IntegerComputedClassCell.leftNumerator ![(1/512),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/512),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/512),0,0] ![(1/1024),1,1])) := by decide +kernel
#print axioms leaf01363_transform
theorem leaf01363_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01363=true := by decide +kernel
#print axioms leaf01363_sign
theorem leaf01363_log : RationalLog.accepts (536875003/536870912) (16363/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01363_log
def leaf01363 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (291/40000000000) (536875003/536870912) (16363/4294967296) 0 8 ![60,0,4] ![(1/512),0,0] ![(1/1024),1,1] affine01363
theorem leaf01363_checked : FastNestedCellData.accepts 1 2 4 leaf01363=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (291/40000000000) (536875003/536870912) (16363/4294967296) 0 8 ![60,0,4] ![(1/512),0,0] ![(1/1024),1,1] 3355001578405924700160000000000 3355027168198554718117577097216 461172119340007521390732247040000000000 raw01363 affine01363
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01363_raw leaf01363_rectangular
    leaf01363_transform leaf01363_sign leaf01363_log
#print axioms leaf01363_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
