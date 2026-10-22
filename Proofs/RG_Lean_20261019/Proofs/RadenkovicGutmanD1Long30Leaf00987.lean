/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00987 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10664179791628837860427681497088000000000000 5699420604267039679391551934792418885369856 9858775387289562867246397652992000000000000))
theorem leaf00987_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10664179791628837860427681497088000000000000 5699420604267039679391551934792418885369856 9858775387289562867246397652992000000000000 raw00987=true := by decide +kernel
#print axioms leaf00987_raw
theorem leaf00987_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00987=true := by decide +kernel
#print axioms leaf00987_rectangular
def affine00987 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00987 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/8)] ![(1/160),1,(1/8)]))
theorem leaf00987_transform : affine00987=(NestedInteger.clearedAll 3 raw00987 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/8)] ![(1/160),1,(1/8)])) := by decide +kernel
#print axioms leaf00987_transform
theorem leaf00987_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00987=true := by decide +kernel
#print axioms leaf00987_sign
theorem leaf00987_log : RationalLog.accepts (1454543939/4294967296) (-581297821/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00987_log
def leaf00987 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (578106344893/1000000000000) (1454543939/4294967296) (-581297821/1073741824) 2 8 ![60,0,4] ![(21/160),0,(1/8)] ![(1/160),1,(1/8)] affine00987
theorem leaf00987_checked : FastNestedCellData.accepts 1 2 4 leaf00987=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (578106344893/1000000000000) (1454543939/4294967296) (-581297821/1073741824) 2 8 ![60,0,4] ![(21/160),0,(1/8)] ![(1/160),1,(1/8)] 10664179791628837860427681497088000000000000 5699420604267039679391551934792418885369856 9858775387289562867246397652992000000000000 raw00987 affine00987
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00987_raw leaf00987_rectangular
    leaf00987_transform leaf00987_sign leaf00987_log
#print axioms leaf00987_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
