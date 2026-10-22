/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00216 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 32800370520817656759919942041600000000000 23820341998531037812552468209498656342016 167455331151005958191974449152000000000000))
theorem leaf00216_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 32800370520817656759919942041600000000000 23820341998531037812552468209498656342016 167455331151005958191974449152000000000000 raw00216=true := by decide +kernel
#print axioms leaf00216_raw
theorem leaf00216_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00216=true := by decide +kernel
#print axioms leaf00216_rectangular
def affine00216 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00216 (IntegerComputedClassCell.leftNumerator ![(29/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/6400),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00216_transform : affine00216=(NestedInteger.clearedAll 3 raw00216 (IntegerComputedClassCell.leftNumerator ![(29/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/6400),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00216_transform
theorem leaf00216_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00216=true := by decide +kernel
#print axioms leaf00216_sign
theorem leaf00216_log : RationalLog.accepts (2730664495/4294967296) (-972593139/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00216_log
def leaf00216 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (35562232977/250000000000) (2730664495/4294967296) (-972593139/4294967296) 1 8 ![60,0,4] ![(29/6400),0,(1/16)] ![(3/32000),1,(1/16)] affine00216
theorem leaf00216_checked : FastNestedCellData.accepts 1 2 4 leaf00216=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (35562232977/250000000000) (2730664495/4294967296) (-972593139/4294967296) 1 8 ![60,0,4] ![(29/6400),0,(1/16)] ![(3/32000),1,(1/16)] 32800370520817656759919942041600000000000 23820341998531037812552468209498656342016 167455331151005958191974449152000000000000 raw00216 affine00216
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00216_raw leaf00216_rectangular
    leaf00216_transform leaf00216_sign leaf00216_log
#print axioms leaf00216_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
