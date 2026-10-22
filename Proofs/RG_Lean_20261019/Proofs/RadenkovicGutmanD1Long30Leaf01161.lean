/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01161 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1317386005845783578510027128832000000000000 1686262232191260665961337224887985160323072 23611946460918856512953684852736000000000000))
theorem leaf01161_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1317386005845783578510027128832000000000000 1686262232191260665961337224887985160323072 23611946460918856512953684852736000000000000 raw01161=true := by decide +kernel
#print axioms leaf01161_raw
theorem leaf01161_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01161=true := by decide +kernel
#print axioms leaf01161_rectangular
def affine01161 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01161 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01161_transform : affine01161=(NestedInteger.clearedAll 3 raw01161 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01161_transform
theorem leaf01161_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01161=true := by decide +kernel
#print axioms leaf01161_sign
theorem leaf01161_log : RationalLog.accepts (5131140983/4294967296) (382003211/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01161_log
def leaf01161 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (71415638477/1000000000000) (5131140983/4294967296) (382003211/4294967296) 0 8 ![60,0,4] ![(3/4),0,(1/2)] ![(1/16),1,(1/4)] affine01161
theorem leaf01161_checked : FastNestedCellData.accepts 1 2 4 leaf01161=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (71415638477/1000000000000) (5131140983/4294967296) (382003211/4294967296) 0 8 ![60,0,4] ![(3/4),0,(1/2)] ![(1/16),1,(1/4)] 1317386005845783578510027128832000000000000 1686262232191260665961337224887985160323072 23611946460918856512953684852736000000000000 raw01161 affine01161
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01161_raw leaf01161_rectangular
    leaf01161_transform leaf01161_sign leaf01161_log
#print axioms leaf01161_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
