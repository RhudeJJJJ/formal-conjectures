/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00902 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 106847746464508046869857409433600000000000 41524506098795943205016261370055426572288 71690041403551937063910427852800000000000))
theorem leaf00902_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 106847746464508046869857409433600000000000 41524506098795943205016261370055426572288 71690041403551937063910427852800000000000 raw00902=true := by decide +kernel
#print axioms leaf00902_raw
theorem leaf00902_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00902=true := by decide +kernel
#print axioms leaf00902_rectangular
def affine00902 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00902 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00902_transform : affine00902=(NestedInteger.clearedAll 3 raw00902 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00902_transform
theorem leaf00902_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00902=true := by decide +kernel
#print axioms leaf00902_sign
theorem leaf00902_log : RationalLog.accepts (1056952733/4294967296) (-1505444023/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00902_log
def leaf00902 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (57922279421/100000000000) (1056952733/4294967296) (-1505444023/2147483648) 3 8 ![60,0,4] ![(11/160),0,(1/8)] ![(1/640),1,(1/8)] affine00902
theorem leaf00902_checked : FastNestedCellData.accepts 1 2 4 leaf00902=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (57922279421/100000000000) (1056952733/4294967296) (-1505444023/2147483648) 3 8 ![60,0,4] ![(11/160),0,(1/8)] ![(1/640),1,(1/8)] 106847746464508046869857409433600000000000 41524506098795943205016261370055426572288 71690041403551937063910427852800000000000 raw00902 affine00902
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00902_raw leaf00902_rectangular
    leaf00902_transform leaf00902_sign leaf00902_log
#print axioms leaf00902_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
