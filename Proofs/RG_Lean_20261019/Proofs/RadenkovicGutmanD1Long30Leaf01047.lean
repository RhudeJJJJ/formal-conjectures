/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01047 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7812188476363933954029547159552000000000000 6731861116115856876835279469045909483945984 15895791496129404482904519606272000000000000))
theorem leaf01047_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7812188476363933954029547159552000000000000 6731861116115856876835279469045909483945984 15895791496129404482904519606272000000000000 raw01047=true := by decide +kernel
#print axioms leaf01047_raw
theorem leaf01047_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01047=true := by decide +kernel
#print axioms leaf01047_rectangular
def affine01047 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01047 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/8)] ![(3/160),1,(1/8)]))
theorem leaf01047_transform : affine01047=(NestedInteger.clearedAll 3 raw01047 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/8)] ![(3/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01047_transform
theorem leaf01047_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01047=true := by decide +kernel
#print axioms leaf01047_sign
theorem leaf01047_log : RationalLog.accepts (2599949731/4294967296) (-134741673/536870912) 1 8=true := by decide +kernel
#print axioms leaf01047_log
def leaf01047 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (423499585897/1000000000000) (2599949731/4294967296) (-134741673/536870912) 1 8 ![60,0,4] ![(41/160),0,(1/8)] ![(3/160),1,(1/8)] affine01047
theorem leaf01047_checked : FastNestedCellData.accepts 1 2 4 leaf01047=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (423499585897/1000000000000) (2599949731/4294967296) (-134741673/536870912) 1 8 ![60,0,4] ![(41/160),0,(1/8)] ![(3/160),1,(1/8)] 7812188476363933954029547159552000000000000 6731861116115856876835279469045909483945984 15895791496129404482904519606272000000000000 raw01047 affine01047
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01047_raw leaf01047_rectangular
    leaf01047_transform leaf01047_sign leaf01047_log
#print axioms leaf01047_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
