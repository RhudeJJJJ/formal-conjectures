/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01209 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1054754133634877270226108416000000000000 1214475600521471790896005995002345816064 82969278811699755810652422144000000000000))
theorem leaf01209_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1054754133634877270226108416000000000000 1214475600521471790896005995002345816064 82969278811699755810652422144000000000000 raw01209=true := by decide +kernel
#print axioms leaf01209_raw
theorem leaf01209_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01209=true := by decide +kernel
#print axioms leaf01209_rectangular
def affine01209 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01209 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/32),0,(15/16)] ![(1/64),1,(1/16)]))
theorem leaf01209_transform : affine01209=(NestedInteger.clearedAll 3 raw01209 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/32),0,(15/16)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01209_transform
theorem leaf01209_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01209=true := by decide +kernel
#print axioms leaf01209_sign
theorem leaf01209_log : RationalLog.accepts (2437005157/2147483648) (271598979/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01209_log
def leaf01209 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1829706757/125000000000) (2437005157/2147483648) (271598979/4294967296) 0 8 ![60,0,4] ![(11/32),0,(15/16)] ![(1/64),1,(1/16)] affine01209
theorem leaf01209_checked : FastNestedCellData.accepts 1 2 4 leaf01209=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1829706757/125000000000) (2437005157/2147483648) (271598979/4294967296) 0 8 ![60,0,4] ![(11/32),0,(15/16)] ![(1/64),1,(1/16)] 1054754133634877270226108416000000000000 1214475600521471790896005995002345816064 82969278811699755810652422144000000000000 raw01209 affine01209
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01209_raw leaf01209_rectangular
    leaf01209_transform leaf01209_sign leaf01209_log
#print axioms leaf01209_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
