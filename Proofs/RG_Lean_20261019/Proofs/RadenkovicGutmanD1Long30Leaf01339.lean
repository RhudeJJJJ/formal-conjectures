/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01339 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 45192902261183300384063488000000000000 45579405422237891585534743328153665536 290695408179324514842357792768000000000000))
theorem leaf01339_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 45192902261183300384063488000000000000 45579405422237891585534743328153665536 290695408179324514842357792768000000000000 raw01339=true := by decide +kernel
#print axioms leaf01339_raw
theorem leaf01339_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01339=true := by decide +kernel
#print axioms leaf01339_rectangular
def affine01339 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01339 (IntegerComputedClassCell.leftNumerator ![(17/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(17/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(17/256),0,0] ![(1/256),1,1]))
theorem leaf01339_transform : affine01339=(NestedInteger.clearedAll 3 raw01339 (IntegerComputedClassCell.leftNumerator ![(17/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(17/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(17/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01339_transform
theorem leaf01339_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01339=true := by decide +kernel
#print axioms leaf01339_sign
theorem leaf01339_log : RationalLog.accepts (541377507/536870912) (8975571/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01339_log
def leaf01339 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (156794377/1000000000000) (541377507/536870912) (8975571/2147483648) 0 8 ![60,0,4] ![(17/256),0,0] ![(1/256),1,1] affine01339
theorem leaf01339_checked : FastNestedCellData.accepts 1 2 4 leaf01339=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (156794377/1000000000000) (541377507/536870912) (8975571/2147483648) 0 8 ![60,0,4] ![(17/256),0,0] ![(1/256),1,1] 45192902261183300384063488000000000000 45579405422237891585534743328153665536 290695408179324514842357792768000000000000 raw01339 affine01339
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01339_raw leaf01339_rectangular
    leaf01339_transform leaf01339_sign leaf01339_log
#print axioms leaf01339_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
