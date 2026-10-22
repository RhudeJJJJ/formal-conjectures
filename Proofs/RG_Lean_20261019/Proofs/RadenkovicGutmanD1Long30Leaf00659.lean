/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00659 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 162561543966299142043467776000000000 133606515691519081678046498931081216 1480572193402240436168294400000000000))
theorem leaf00659_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 162561543966299142043467776000000000 133606515691519081678046498931081216 1480572193402240436168294400000000000 raw00659=true := by decide +kernel
#print axioms leaf00659_raw
theorem leaf00659_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00659=true := by decide +kernel
#print axioms leaf00659_rectangular
def affine00659 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00659 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00659_transform : affine00659=(NestedInteger.clearedAll 3 raw00659 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00659_transform
theorem leaf00659_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00659=true := by decide +kernel
#print axioms leaf00659_sign
theorem leaf00659_log : RationalLog.accepts (25295175/33554432) (-606782901/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00659_log
def leaf00659 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18047956903/200000000000) (25295175/33554432) (-606782901/4294967296) 1 8 ![60,0,4] ![(79/3200),0,(1/2)] ![(3/6400),1,(1/2)] affine00659
theorem leaf00659_checked : FastNestedCellData.accepts 1 2 4 leaf00659=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18047956903/200000000000) (25295175/33554432) (-606782901/4294967296) 1 8 ![60,0,4] ![(79/3200),0,(1/2)] ![(3/6400),1,(1/2)] 162561543966299142043467776000000000 133606515691519081678046498931081216 1480572193402240436168294400000000000 raw00659 affine00659
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00659_raw leaf00659_rectangular
    leaf00659_transform leaf00659_sign leaf00659_log
#print axioms leaf00659_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
