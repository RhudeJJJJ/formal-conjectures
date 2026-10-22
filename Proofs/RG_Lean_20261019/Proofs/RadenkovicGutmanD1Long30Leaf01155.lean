/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01155 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 93107487486472128176131670016000000000000 119406753005853340832188745221888360316928 1478577255730679931498143940608000000000000))
theorem leaf01155_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 93107487486472128176131670016000000000000 119406753005853340832188745221888360316928 1478577255730679931498143940608000000000000 raw01155=true := by decide +kernel
#print axioms leaf01155_raw
theorem leaf01155_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01155=true := by decide +kernel
#print axioms leaf01155_rectangular
def affine01155 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01155 (IntegerComputedClassCell.leftNumerator ![(13/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/16),0,0] ![(1/16),1,(1/2)]))
theorem leaf01155_transform : affine01155=(NestedInteger.clearedAll 3 raw01155 (IntegerComputedClassCell.leftNumerator ![(13/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/16),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01155_transform
theorem leaf01155_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01155=true := by decide +kernel
#print axioms leaf01155_sign
theorem leaf01155_log : RationalLog.accepts (2548271749/2147483648) (367474445/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01155_log
def leaf01155 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (40378936083/500000000000) (2548271749/2147483648) (367474445/4294967296) 0 8 ![60,0,4] ![(13/16),0,0] ![(1/16),1,(1/2)] affine01155
theorem leaf01155_checked : FastNestedCellData.accepts 1 2 4 leaf01155=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (40378936083/500000000000) (2548271749/2147483648) (367474445/4294967296) 0 8 ![60,0,4] ![(13/16),0,0] ![(1/16),1,(1/2)] 93107487486472128176131670016000000000000 119406753005853340832188745221888360316928 1478577255730679931498143940608000000000000 raw01155 affine01155
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01155_raw leaf01155_rectangular
    leaf01155_transform leaf01155_sign leaf01155_log
#print axioms leaf01155_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
