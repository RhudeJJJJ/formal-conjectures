/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00045 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 138348095762559850388115161088000000000000 23714752144496354106330935980739002368 197626483928883628695617536000000000000))
theorem leaf00045_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 138348095762559850388115161088000000000000 23714752144496354106330935980739002368 197626483928883628695617536000000000000 raw00045=true := by decide +kernel
#print axioms leaf00045_raw
theorem leaf00045_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00045=true := by decide +kernel
#print axioms leaf00045_rectangular
def affine00045 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00045 (IntegerComputedClassCell.leftNumerator ![(1/200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/200),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00045_transform : affine00045=(NestedInteger.clearedAll 3 raw00045 (IntegerComputedClassCell.leftNumerator ![(1/200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/200),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00045_transform
theorem leaf00045_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00045=true := by decide +kernel
#print axioms leaf00045_sign
theorem leaf00045_log : RationalLog.accepts (657337/4294967296) (-4716280979/1073741824) 13 8=true := by decide +kernel
#print axioms leaf00045_log
def leaf00045 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (29999461197/250000000000) (657337/4294967296) (-4716280979/1073741824) 13 8 ![52,0,4] ![(1/200),0,0] ![(1/3200),1,(1/4)] affine00045
theorem leaf00045_checked : FastNestedCellData.accepts 1 0 4 leaf00045=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (29999461197/250000000000) (657337/4294967296) (-4716280979/1073741824) 13 8 ![52,0,4] ![(1/200),0,0] ![(1/3200),1,(1/4)] 138348095762559850388115161088000000000000 23714752144496354106330935980739002368 197626483928883628695617536000000000000 raw00045 affine00045
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00045_raw leaf00045_rectangular
    leaf00045_transform leaf00045_sign leaf00045_log
#print axioms leaf00045_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
