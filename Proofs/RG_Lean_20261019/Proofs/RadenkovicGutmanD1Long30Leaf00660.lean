/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00660 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 194088277746043612717855539200000000000 4547939775362575873194981894052118528 5276490707085959188447232000000000000))
theorem leaf00660_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 194088277746043612717855539200000000000 4547939775362575873194981894052118528 5276490707085959188447232000000000000 raw00660=true := by decide +kernel
#print axioms leaf00660_raw
theorem leaf00660_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00660=true := by decide +kernel
#print axioms leaf00660_rectangular
def affine00660 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00660 (IntegerComputedClassCell.leftNumerator ![(161/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(161/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(161/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00660_transform : affine00660=(NestedInteger.clearedAll 3 raw00660 (IntegerComputedClassCell.leftNumerator ![(161/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(161/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(161/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00660_transform
theorem leaf00660_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00660=true := by decide +kernel
#print axioms leaf00660_sign
theorem leaf00660_log : RationalLog.accepts (844565/67108864) (-9395777463/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00660_log
def leaf00660 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (430962549527/500000000000) (844565/67108864) (-9395777463/4294967296) 7 8 ![60,0,4] ![(161/6400),0,0] ![(3/6400),1,(1/16)] affine00660
theorem leaf00660_checked : FastNestedCellData.accepts 1 2 4 leaf00660=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (430962549527/500000000000) (844565/67108864) (-9395777463/4294967296) 7 8 ![60,0,4] ![(161/6400),0,0] ![(3/6400),1,(1/16)] 194088277746043612717855539200000000000 4547939775362575873194981894052118528 5276490707085959188447232000000000000 raw00660 affine00660
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00660_raw leaf00660_rectangular
    leaf00660_transform leaf00660_sign leaf00660_log
#print axioms leaf00660_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
