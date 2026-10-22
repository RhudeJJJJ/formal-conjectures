/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01083 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1036862342350232798955883724800000000000 1090435304120231055114736015585755267072 3789034535231447993419825152000000000000))
theorem leaf01083_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1036862342350232798955883724800000000000 1090435304120231055114736015585755267072 3789034535231447993419825152000000000000 raw01083=true := by decide +kernel
#print axioms leaf01083_raw
theorem leaf01083_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01083=true := by decide +kernel
#print axioms leaf01083_rectangular
def affine01083 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01083 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)]))
theorem leaf01083_transform : affine01083=(NestedInteger.clearedAll 3 raw01083 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf01083_transform
theorem leaf01083_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01083=true := by decide +kernel
#print axioms leaf01083_sign
theorem leaf01083_log : RationalLog.accepts (109608595/134217728) (-108741883/1073741824) 1 8=true := by decide +kernel
#print axioms leaf01083_log
def leaf01083 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (287787111461/1000000000000) (109608595/134217728) (-108741883/1073741824) 1 8 ![60,0,4] ![(31/80),0,(1/4)] ![(3/80),1,(1/4)] affine01083
theorem leaf01083_checked : FastNestedCellData.accepts 1 2 4 leaf01083=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (287787111461/1000000000000) (109608595/134217728) (-108741883/1073741824) 1 8 ![60,0,4] ![(31/80),0,(1/4)] ![(3/80),1,(1/4)] 1036862342350232798955883724800000000000 1090435304120231055114736015585755267072 3789034535231447993419825152000000000000 raw01083 affine01083
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01083_raw leaf01083_rectangular
    leaf01083_transform leaf01083_sign leaf01083_log
#print axioms leaf01083_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
