/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00294 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1764317888634441734054477824000000000000 1665954803553818665523085474595650666496 68040286670181656208074604544000000000000))
theorem leaf00294_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1764317888634441734054477824000000000000 1665954803553818665523085474595650666496 68040286670181656208074604544000000000000 raw00294=true := by decide +kernel
#print axioms leaf00294_raw
theorem leaf00294_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00294=true := by decide +kernel
#print axioms leaf00294_rectangular
def affine00294 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00294 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00294_transform : affine00294=(NestedInteger.clearedAll 3 raw00294 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00294_transform
theorem leaf00294_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00294=true := by decide +kernel
#print axioms leaf00294_sign
theorem leaf00294_log : RationalLog.accepts (989647919/1073741824) (-175139389/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00294_log
def leaf00294 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6121207321/250000000000) (989647919/1073741824) (-175139389/4294967296) 1 8 ![60,0,4] ![(21/3200),0,(1/2)] ![(1/6400),1,(1/2)] affine00294
theorem leaf00294_checked : FastNestedCellData.accepts 1 2 4 leaf00294=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6121207321/250000000000) (989647919/1073741824) (-175139389/4294967296) 1 8 ![60,0,4] ![(21/3200),0,(1/2)] ![(1/6400),1,(1/2)] 1764317888634441734054477824000000000000 1665954803553818665523085474595650666496 68040286670181656208074604544000000000000 raw00294 affine00294
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00294_raw leaf00294_rectangular
    leaf00294_transform leaf00294_sign leaf00294_log
#print axioms leaf00294_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
