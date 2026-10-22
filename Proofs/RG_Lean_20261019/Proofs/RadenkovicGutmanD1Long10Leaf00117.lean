/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00117 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 5435496261984100197666624897024000000000000 13623350498417270670749373963727552905216 46234317522833386229196652544000000000000))
theorem leaf00117_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 5435496261984100197666624897024000000000000 13623350498417270670749373963727552905216 46234317522833386229196652544000000000000 raw00117=true := by decide +kernel
#print axioms leaf00117_raw
theorem leaf00117_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00117=true := by decide +kernel
#print axioms leaf00117_rectangular
def affine00117 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00117 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/1600),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00117_transform : affine00117=(NestedInteger.clearedAll 3 raw00117 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/1600),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00117_transform
theorem leaf00117_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00117=true := by decide +kernel
#print axioms leaf00117_sign
theorem leaf00117_log : RationalLog.accepts (8314751/4294967296) (-3353922899/1073741824) 10 8=true := by decide +kernel
#print axioms leaf00117_log
def leaf00117 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (294658842789/1000000000000) (8314751/4294967296) (-3353922899/1073741824) 10 8 ![52,0,4] ![(21/1600),0,0] ![(1/1600),1,(1/4)] affine00117
theorem leaf00117_checked : FastNestedCellData.accepts 1 0 4 leaf00117=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (294658842789/1000000000000) (8314751/4294967296) (-3353922899/1073741824) 10 8 ![52,0,4] ![(21/1600),0,0] ![(1/1600),1,(1/4)] 5435496261984100197666624897024000000000000 13623350498417270670749373963727552905216 46234317522833386229196652544000000000000 raw00117 affine00117
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00117_raw leaf00117_rectangular
    leaf00117_transform leaf00117_sign leaf00117_log
#print axioms leaf00117_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
