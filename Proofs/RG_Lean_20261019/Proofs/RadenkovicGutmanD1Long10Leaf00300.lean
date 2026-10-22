/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00300 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2612664410275263536585031601356800000000000 422123482875162335372368342676833151483904 596081442796600025503022186496000000000000))
theorem leaf00300_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2612664410275263536585031601356800000000000 422123482875162335372368342676833151483904 596081442796600025503022186496000000000000 raw00300=true := by decide +kernel
#print axioms leaf00300_raw
theorem leaf00300_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00300=true := by decide +kernel
#print axioms leaf00300_rectangular
def affine00300 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00300 (IntegerComputedClassCell.leftNumerator ![(13/160),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/160),0,0] ![(1/320),1,(1/4)]))
theorem leaf00300_transform : affine00300=(NestedInteger.clearedAll 3 raw00300 (IntegerComputedClassCell.leftNumerator ![(13/160),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/160),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00300_transform
theorem leaf00300_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00300=true := by decide +kernel
#print axioms leaf00300_sign
theorem leaf00300_log : RationalLog.accepts (406243245/4294967296) (-5064297257/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00300_log
def leaf00300 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (708164107399/1000000000000) (406243245/4294967296) (-5064297257/4294967296) 4 8 ![52,0,4] ![(13/160),0,0] ![(1/320),1,(1/4)] affine00300
theorem leaf00300_checked : FastNestedCellData.accepts 1 0 4 leaf00300=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (708164107399/1000000000000) (406243245/4294967296) (-5064297257/4294967296) 4 8 ![52,0,4] ![(13/160),0,0] ![(1/320),1,(1/4)] 2612664410275263536585031601356800000000000 422123482875162335372368342676833151483904 596081442796600025503022186496000000000000 raw00300 affine00300
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00300_raw leaf00300_rectangular
    leaf00300_transform leaf00300_sign leaf00300_log
#print axioms leaf00300_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
