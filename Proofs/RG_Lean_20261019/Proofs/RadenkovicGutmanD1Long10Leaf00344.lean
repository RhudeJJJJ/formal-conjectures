/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00344 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8379709111023957689419956224000000000000 5731580719363568863206954426535155597312 16428729255378175424259424256000000000000))
theorem leaf00344_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8379709111023957689419956224000000000000 5731580719363568863206954426535155597312 16428729255378175424259424256000000000000 raw00344=true := by decide +kernel
#print axioms leaf00344_raw
theorem leaf00344_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00344=true := by decide +kernel
#print axioms leaf00344_rectangular
def affine00344 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00344 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00344_transform : affine00344=(NestedInteger.clearedAll 3 raw00344 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00344_transform
theorem leaf00344_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00344=true := by decide +kernel
#print axioms leaf00344_sign
theorem leaf00344_log : RationalLog.accepts (272234703/536870912) (-1458341375/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00344_log
def leaf00344 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (174437737401/500000000000) (272234703/536870912) (-1458341375/4294967296) 1 8 ![52,0,4] ![(23/160),0,(1/2)] ![(1/160),1,(1/2)] affine00344
theorem leaf00344_checked : FastNestedCellData.accepts 1 0 4 leaf00344=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (174437737401/500000000000) (272234703/536870912) (-1458341375/4294967296) 1 8 ![52,0,4] ![(23/160),0,(1/2)] ![(1/160),1,(1/2)] 8379709111023957689419956224000000000000 5731580719363568863206954426535155597312 16428729255378175424259424256000000000000 raw00344 affine00344
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00344_raw leaf00344_rectangular
    leaf00344_transform leaf00344_sign leaf00344_log
#print axioms leaf00344_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
