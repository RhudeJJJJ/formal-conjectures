/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00933 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 122794712002184241012820410368000000000000 65112068107187407092442830848121039224832 152834560841811107800317689856000000000000))
theorem leaf00933_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 122794712002184241012820410368000000000000 65112068107187407092442830848121039224832 152834560841811107800317689856000000000000 raw00933=true := by decide +kernel
#print axioms leaf00933_raw
theorem leaf00933_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00933=true := by decide +kernel
#print axioms leaf00933_rectangular
def affine00933 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00933 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00933_transform : affine00933=(NestedInteger.clearedAll 3 raw00933 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00933_transform
theorem leaf00933_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00933=true := by decide +kernel
#print axioms leaf00933_sign
theorem leaf00933_log : RationalLog.accepts (1597030107/4294967296) (-2124501821/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00933_log
def leaf00933 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (53253717409/125000000000) (1597030107/4294967296) (-2124501821/4294967296) 2 8 ![60,0,4] ![(27/320),0,(1/4)] ![(1/320),1,(1/4)] affine00933
theorem leaf00933_checked : FastNestedCellData.accepts 1 2 4 leaf00933=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (53253717409/125000000000) (1597030107/4294967296) (-2124501821/4294967296) 2 8 ![60,0,4] ![(27/320),0,(1/4)] ![(1/320),1,(1/4)] 122794712002184241012820410368000000000000 65112068107187407092442830848121039224832 152834560841811107800317689856000000000000 raw00933 affine00933
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00933_raw leaf00933_rectangular
    leaf00933_transform leaf00933_sign leaf00933_log
#print axioms leaf00933_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
