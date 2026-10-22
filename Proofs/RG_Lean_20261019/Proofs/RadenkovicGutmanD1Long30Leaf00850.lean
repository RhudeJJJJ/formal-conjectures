/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00850 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 490520407685197635501686784000000000 49392068633418244987298040105664512 56685231237942074146816000000000000))
theorem leaf00850_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 490520407685197635501686784000000000 49392068633418244987298040105664512 56685231237942074146816000000000000 raw00850=true := by decide +kernel
#print axioms leaf00850_raw
theorem leaf00850_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00850=true := by decide +kernel
#print axioms leaf00850_rectangular
def affine00850 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00850 (IntegerComputedClassCell.leftNumerator ![(17/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/320),0,0] ![(1/640),1,(1/16)]))
theorem leaf00850_transform : affine00850=(NestedInteger.clearedAll 3 raw00850 (IntegerComputedClassCell.leftNumerator ![(17/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/320),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00850_transform
theorem leaf00850_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00850=true := by decide +kernel
#print axioms leaf00850_sign
theorem leaf00850_log : RationalLog.accepts (451375/8388608) (-1568914765/1073741824) 5 8=true := by decide +kernel
#print axioms leaf00850_log
def leaf00850 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (871339281057/1000000000000) (451375/8388608) (-1568914765/1073741824) 5 8 ![60,0,4] ![(17/320),0,0] ![(1/640),1,(1/16)] affine00850
theorem leaf00850_checked : FastNestedCellData.accepts 1 2 4 leaf00850=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (871339281057/1000000000000) (451375/8388608) (-1568914765/1073741824) 5 8 ![60,0,4] ![(17/320),0,0] ![(1/640),1,(1/16)] 490520407685197635501686784000000000 49392068633418244987298040105664512 56685231237942074146816000000000000 raw00850 affine00850
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00850_raw leaf00850_rectangular
    leaf00850_transform leaf00850_sign leaf00850_log
#print axioms leaf00850_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
