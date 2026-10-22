/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00377 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 163628642107449650752234979328000000000000 119431765422703542136701573019367481802752 841511907179277382875437072384000000000000))
theorem leaf00377_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 163628642107449650752234979328000000000000 119431765422703542136701573019367481802752 841511907179277382875437072384000000000000 raw00377=true := by decide +kernel
#print axioms leaf00377_raw
theorem leaf00377_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00377=true := by decide +kernel
#print axioms leaf00377_rectangular
def affine00377 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00377 (IntegerComputedClassCell.leftNumerator ![(59/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(59/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(59/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00377_transform : affine00377=(NestedInteger.clearedAll 3 raw00377 (IntegerComputedClassCell.leftNumerator ![(59/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(59/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(59/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00377_transform
theorem leaf00377_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00377=true := by decide +kernel
#print axioms leaf00377_sign
theorem leaf00377_log : RationalLog.accepts (686313797/1073741824) (-480574545/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00377_log
def leaf00377 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (141925223403/1000000000000) (686313797/1073741824) (-480574545/2147483648) 1 8 ![60,0,4] ![(59/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00377
theorem leaf00377_checked : FastNestedCellData.accepts 1 2 4 leaf00377=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (141925223403/1000000000000) (686313797/1073741824) (-480574545/2147483648) 1 8 ![60,0,4] ![(59/6400),0,(1/8)] ![(1/6400),1,(1/8)] 163628642107449650752234979328000000000000 119431765422703542136701573019367481802752 841511907179277382875437072384000000000000 raw00377 affine00377
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00377_raw leaf00377_rectangular
    leaf00377_transform leaf00377_sign leaf00377_log
#print axioms leaf00377_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
