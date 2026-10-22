/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00926 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3336427993048836481788751642624000000000000 1073827161037763081124036120349366504390656 1484268120002235180208908926976000000000000))
theorem leaf00926_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3336427993048836481788751642624000000000000 1073827161037763081124036120349366504390656 1484268120002235180208908926976000000000000 raw00926=true := by decide +kernel
#print axioms leaf00926_raw
theorem leaf00926_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00926=true := by decide +kernel
#print axioms leaf00926_rectangular
def affine00926 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00926 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00926_transform : affine00926=(NestedInteger.clearedAll 3 raw00926 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00926_transform
theorem leaf00926_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00926=true := by decide +kernel
#print axioms leaf00926_sign
theorem leaf00926_log : RationalLog.accepts (401031177/2147483648) (-3603505299/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00926_log
def leaf00926 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (723472495681/1000000000000) (401031177/2147483648) (-3603505299/4294967296) 3 8 ![60,0,4] ![(13/160),0,(1/16)] ![(1/320),1,(1/16)] affine00926
theorem leaf00926_checked : FastNestedCellData.accepts 1 2 4 leaf00926=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (723472495681/1000000000000) (401031177/2147483648) (-3603505299/4294967296) 3 8 ![60,0,4] ![(13/160),0,(1/16)] ![(1/320),1,(1/16)] 3336427993048836481788751642624000000000000 1073827161037763081124036120349366504390656 1484268120002235180208908926976000000000000 raw00926 affine00926
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00926_raw leaf00926_rectangular
    leaf00926_transform leaf00926_sign leaf00926_log
#print axioms leaf00926_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
