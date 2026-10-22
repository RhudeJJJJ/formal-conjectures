/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00770 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1015571203669785377969186799616000000000000 50978613978675349955376906322347139530752 57873185177645700656421404672000000000000))
theorem leaf00770_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1015571203669785377969186799616000000000000 50978613978675349955376906322347139530752 57873185177645700656421404672000000000000 raw00770=true := by decide +kernel
#print axioms leaf00770_raw
theorem leaf00770_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00770=true := by decide +kernel
#print axioms leaf00770_rectangular
def affine00770 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00770 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/1600),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00770_transform : affine00770=(NestedInteger.clearedAll 3 raw00770 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/1600),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00770_transform
theorem leaf00770_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00770=true := by decide +kernel
#print axioms leaf00770_sign
theorem leaf00770_log : RationalLog.accepts (57312491/2147483648) (-1945369759/1073741824) 6 8=true := by decide +kernel
#print axioms leaf00770_log
def leaf00770 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (440433802133/500000000000) (57312491/2147483648) (-1945369759/1073741824) 6 8 ![60,0,4] ![(59/1600),0,0] ![(3/3200),1,(1/16)] affine00770
theorem leaf00770_checked : FastNestedCellData.accepts 1 2 4 leaf00770=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (440433802133/500000000000) (57312491/2147483648) (-1945369759/1073741824) 6 8 ![60,0,4] ![(59/1600),0,0] ![(3/3200),1,(1/16)] 1015571203669785377969186799616000000000000 50978613978675349955376906322347139530752 57873185177645700656421404672000000000000 raw00770 affine00770
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00770_raw leaf00770_rectangular
    leaf00770_transform leaf00770_sign leaf00770_log
#print axioms leaf00770_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
