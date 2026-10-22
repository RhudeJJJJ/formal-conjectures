/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00059 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 18289821195931168741628313600000000000 18012061861182199596680702416392290304 2838531503343180349473135001600000000000))
theorem leaf00059_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 18289821195931168741628313600000000000 18012061861182199596680702416392290304 2838531503343180349473135001600000000000 raw00059=true := by decide +kernel
#print axioms leaf00059_raw
theorem leaf00059_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00059=true := by decide +kernel
#print axioms leaf00059_rectangular
def affine00059 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00059 (IntegerComputedClassCell.leftNumerator ![(27/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/16000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00059_transform : affine00059=(NestedInteger.clearedAll 3 raw00059 (IntegerComputedClassCell.leftNumerator ![(27/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/16000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00059_transform
theorem leaf00059_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00059=true := by decide +kernel
#print axioms leaf00059_sign
theorem leaf00059_log : RationalLog.accepts (2101535363/2147483648) (-46447011/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00059_log
def leaf00059 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (158638911/25000000000) (2101535363/2147483648) (-46447011/4294967296) 1 8 ![60,0,4] ![(27/16000),0,(1/2)] ![(1/16000),1,(1/2)] affine00059
theorem leaf00059_checked : FastNestedCellData.accepts 1 2 4 leaf00059=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (158638911/25000000000) (2101535363/2147483648) (-46447011/4294967296) 1 8 ![60,0,4] ![(27/16000),0,(1/2)] ![(1/16000),1,(1/2)] 18289821195931168741628313600000000000 18012061861182199596680702416392290304 2838531503343180349473135001600000000000 raw00059 affine00059
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00059_raw leaf00059_rectangular
    leaf00059_transform leaf00059_sign leaf00059_log
#print axioms leaf00059_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
