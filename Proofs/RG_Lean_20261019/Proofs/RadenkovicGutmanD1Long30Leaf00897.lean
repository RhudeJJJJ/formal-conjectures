/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00897 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10632154802746550576189875945472000000000000 4116602710975613204708540863268887122149376 7142288470338055134785965129728000000000000))
theorem leaf00897_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10632154802746550576189875945472000000000000 4116602710975613204708540863268887122149376 7142288470338055134785965129728000000000000 raw00897=true := by decide +kernel
#print axioms leaf00897_raw
theorem leaf00897_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00897=true := by decide +kernel
#print axioms leaf00897_rectangular
def affine00897 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00897 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00897_transform : affine00897=(NestedInteger.clearedAll 3 raw00897 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00897_transform
theorem leaf00897_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00897=true := by decide +kernel
#print axioms leaf00897_sign
theorem leaf00897_log : RationalLog.accepts (1054919429/4294967296) (-753755807/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00897_log
def leaf00897 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (576370266767/1000000000000) (1054919429/4294967296) (-753755807/1073741824) 3 8 ![60,0,4] ![(43/640),0,(1/8)] ![(1/640),1,(1/8)] affine00897
theorem leaf00897_checked : FastNestedCellData.accepts 1 2 4 leaf00897=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (576370266767/1000000000000) (1054919429/4294967296) (-753755807/1073741824) 3 8 ![60,0,4] ![(43/640),0,(1/8)] ![(1/640),1,(1/8)] 10632154802746550576189875945472000000000000 4116602710975613204708540863268887122149376 7142288470338055134785965129728000000000000 raw00897 affine00897
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00897_raw leaf00897_rectangular
    leaf00897_transform leaf00897_sign leaf00897_log
#print axioms leaf00897_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
