/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00052 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 29707907447889413754989838336000000000000 27959871252776041599861349815001999736832 1085082713749144994926676672512000000000000))
theorem leaf00052_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 29707907447889413754989838336000000000000 27959871252776041599861349815001999736832 1085082713749144994926676672512000000000000 raw00052=true := by decide +kernel
#print axioms leaf00052_raw
theorem leaf00052_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00052=true := by decide +kernel
#print axioms leaf00052_rectangular
def affine00052 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00052 (IntegerComputedClassCell.leftNumerator ![(13/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/8000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00052_transform : affine00052=(NestedInteger.clearedAll 3 raw00052 (IntegerComputedClassCell.leftNumerator ![(13/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/8000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00052_transform
theorem leaf00052_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00052=true := by decide +kernel
#print axioms leaf00052_sign
theorem leaf00052_log : RationalLog.accepts (3940705957/4294967296) (-46216035/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00052_log
def leaf00052 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6441875559/250000000000) (3940705957/4294967296) (-46216035/1073741824) 1 8 ![60,0,4] ![(13/8000),0,(1/8)] ![(1/16000),1,(1/8)] affine00052
theorem leaf00052_checked : FastNestedCellData.accepts 1 2 4 leaf00052=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6441875559/250000000000) (3940705957/4294967296) (-46216035/1073741824) 1 8 ![60,0,4] ![(13/8000),0,(1/8)] ![(1/16000),1,(1/8)] 29707907447889413754989838336000000000000 27959871252776041599861349815001999736832 1085082713749144994926676672512000000000000 raw00052 affine00052
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00052_raw leaf00052_rectangular
    leaf00052_transform leaf00052_sign leaf00052_log
#print axioms leaf00052_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
