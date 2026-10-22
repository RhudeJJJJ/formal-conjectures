/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01356 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 4714978561868124538273792000000000000 4716269963562453807533244610858975232 4612949128971744670405502173184000000000000))
theorem leaf01356_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 4714978561868124538273792000000000000 4716269963562453807533244610858975232 4612949128971744670405502173184000000000000 raw01356=true := by decide +kernel
#print axioms leaf01356_raw
theorem leaf01356_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01356=true := by decide +kernel
#print axioms leaf01356_rectangular
def affine01356 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01356 (IntegerComputedClassCell.leftNumerator ![(3/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(3/256),0,0] ![(1/512),1,1]))
theorem leaf01356_transform : affine01356=(NestedInteger.clearedAll 3 raw01356 (IntegerComputedClassCell.leftNumerator ![(3/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(3/256),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf01356_transform
theorem leaf01356_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01356=true := by decide +kernel
#print axioms leaf01356_sign
theorem leaf01356_log : RationalLog.accepts (4296139267/4294967296) (585905/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01356_log
def leaf01356 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (511199/500000000000) (4296139267/4294967296) (585905/4294967296) 0 8 ![60,0,4] ![(3/256),0,0] ![(1/512),1,1] affine01356
theorem leaf01356_checked : FastNestedCellData.accepts 1 2 4 leaf01356=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (511199/500000000000) (4296139267/4294967296) (585905/4294967296) 0 8 ![60,0,4] ![(3/256),0,0] ![(1/512),1,1] 4714978561868124538273792000000000000 4716269963562453807533244610858975232 4612949128971744670405502173184000000000000 raw01356 affine01356
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01356_raw leaf01356_rectangular
    leaf01356_transform leaf01356_sign leaf01356_log
#print axioms leaf01356_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
