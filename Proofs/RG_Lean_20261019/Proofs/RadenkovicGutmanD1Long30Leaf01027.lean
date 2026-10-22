/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01027 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 142841301186906232202570235904000000000000 104525508909402487826150576628143354806272 210915376015685953503878971392000000000000))
theorem leaf01027_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 142841301186906232202570235904000000000000 104525508909402487826150576628143354806272 210915376015685953503878971392000000000000 raw01027=true := by decide +kernel
#print axioms leaf01027_raw
theorem leaf01027_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01027=true := by decide +kernel
#print axioms leaf01027_rectangular
def affine01027 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01027 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/8)] ![(3/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/8)] ![(3/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/8)] ![(3/320),1,(1/8)]))
theorem leaf01027_transform : affine01027=(NestedInteger.clearedAll 3 raw01027 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/8)] ![(3/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/8)] ![(3/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/8)] ![(3/320),1,(1/8)])) := by decide +kernel
#print axioms leaf01027_transform
theorem leaf01027_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01027=true := by decide +kernel
#print axioms leaf01027_sign
theorem leaf01027_log : RationalLog.accepts (2101447833/4294967296) (-191882341/536870912) 2 8=true := by decide +kernel
#print axioms leaf01027_log
def leaf01027 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (61947539627/125000000000) (2101447833/4294967296) (-191882341/536870912) 2 8 ![60,0,4] ![(1/5),0,(1/8)] ![(3/320),1,(1/8)] affine01027
theorem leaf01027_checked : FastNestedCellData.accepts 1 2 4 leaf01027=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (61947539627/125000000000) (2101447833/4294967296) (-191882341/536870912) 2 8 ![60,0,4] ![(1/5),0,(1/8)] ![(3/320),1,(1/8)] 142841301186906232202570235904000000000000 104525508909402487826150576628143354806272 210915376015685953503878971392000000000000 raw01027 affine01027
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01027_raw leaf01027_rectangular
    leaf01027_transform leaf01027_sign leaf01027_log
#print axioms leaf01027_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
