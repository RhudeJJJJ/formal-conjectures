/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00477 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5514142366911675427925660794880000000000 3671316682509855274698662784586267754496 19650951244838462590178316779520000000000))
theorem leaf00477_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5514142366911675427925660794880000000000 3671316682509855274698662784586267754496 19650951244838462590178316779520000000000 raw00477=true := by decide +kernel
#print axioms leaf00477_raw
theorem leaf00477_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00477=true := by decide +kernel
#print axioms leaf00477_rectangular
def affine00477 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00477 (IntegerComputedClassCell.leftNumerator ![(79/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(79/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(79/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00477_transform : affine00477=(NestedInteger.clearedAll 3 raw00477 (IntegerComputedClassCell.leftNumerator ![(79/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(79/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(79/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00477_transform
theorem leaf00477_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00477=true := by decide +kernel
#print axioms leaf00477_sign
theorem leaf00477_log : RationalLog.accepts (2409442309/4294967296) (-1241350011/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00477_log
def leaf00477 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7473056417/40000000000) (2409442309/4294967296) (-1241350011/4294967296) 1 8 ![60,0,4] ![(79/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00477
theorem leaf00477_checked : FastNestedCellData.accepts 1 2 4 leaf00477=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7473056417/40000000000) (2409442309/4294967296) (-1241350011/4294967296) 1 8 ![60,0,4] ![(79/6400),0,(1/8)] ![(1/6400),1,(1/8)] 5514142366911675427925660794880000000000 3671316682509855274698662784586267754496 19650951244838462590178316779520000000000 raw00477 affine00477
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00477_raw leaf00477_rectangular
    leaf00477_transform leaf00477_sign leaf00477_log
#print axioms leaf00477_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
