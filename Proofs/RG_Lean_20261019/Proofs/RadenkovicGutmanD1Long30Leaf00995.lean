/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00995 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12502918295490905666167823663104000000000000 6163579181801239721308377338854152194752512 9093714367927686273995687067648000000000000))
theorem leaf00995_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12502918295490905666167823663104000000000000 6163579181801239721308377338854152194752512 9093714367927686273995687067648000000000000 raw00995=true := by decide +kernel
#print axioms leaf00995_raw
theorem leaf00995_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00995=true := by decide +kernel
#print axioms leaf00995_rectangular
def affine00995 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00995 (IntegerComputedClassCell.leftNumerator ![(23/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/160),0,0] ![(1/160),1,(1/16)]))
theorem leaf00995_transform : affine00995=(NestedInteger.clearedAll 3 raw00995 (IntegerComputedClassCell.leftNumerator ![(23/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/160),0,0] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00995_transform
theorem leaf00995_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00995=true := by decide +kernel
#print axioms leaf00995_sign
theorem leaf00995_log : RationalLog.accepts (1261959027/4294967296) (-1315096091/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00995_log
def leaf00995 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (677784558919/1000000000000) (1261959027/4294967296) (-1315096091/2147483648) 2 8 ![60,0,4] ![(23/160),0,0] ![(1/160),1,(1/16)] affine00995
theorem leaf00995_checked : FastNestedCellData.accepts 1 2 4 leaf00995=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (677784558919/1000000000000) (1261959027/4294967296) (-1315096091/2147483648) 2 8 ![60,0,4] ![(23/160),0,0] ![(1/160),1,(1/16)] 12502918295490905666167823663104000000000000 6163579181801239721308377338854152194752512 9093714367927686273995687067648000000000000 raw00995 affine00995
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00995_raw leaf00995_rectangular
    leaf00995_transform leaf00995_sign leaf00995_log
#print axioms leaf00995_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
