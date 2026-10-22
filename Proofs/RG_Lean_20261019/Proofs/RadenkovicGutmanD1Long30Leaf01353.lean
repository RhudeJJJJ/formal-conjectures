/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01353 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 229833316676306110251008000000000000 229974665376908940391721582727266304 72101909837887313115315437568000000000000))
theorem leaf01353_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 229833316676306110251008000000000000 229974665376908940391721582727266304 72101909837887313115315437568000000000000 raw01353=true := by decide +kernel
#print axioms leaf01353_raw
theorem leaf01353_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01353=true := by decide +kernel
#print axioms leaf01353_rectangular
def affine01353 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01353 (IntegerComputedClassCell.leftNumerator ![(9/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(9/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(9/512),0,0] ![(1/512),1,1]))
theorem leaf01353_transform : affine01353=(NestedInteger.clearedAll 3 raw01353 (IntegerComputedClassCell.leftNumerator ![(9/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(9/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(9/512),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf01353_transform
theorem leaf01353_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01353=true := by decide +kernel
#print axioms leaf01353_sign
theorem leaf01353_log : RationalLog.accepts (537199377/536870912) (656729/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01353_log
def leaf01353 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1594789/500000000000) (537199377/536870912) (656729/2147483648) 0 8 ![60,0,4] ![(9/512),0,0] ![(1/512),1,1] affine01353
theorem leaf01353_checked : FastNestedCellData.accepts 1 2 4 leaf01353=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1594789/500000000000) (537199377/536870912) (656729/2147483648) 0 8 ![60,0,4] ![(9/512),0,0] ![(1/512),1,1] 229833316676306110251008000000000000 229974665376908940391721582727266304 72101909837887313115315437568000000000000 raw01353 affine01353
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01353_raw leaf01353_rectangular
    leaf01353_transform leaf01353_sign leaf01353_log
#print axioms leaf01353_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
