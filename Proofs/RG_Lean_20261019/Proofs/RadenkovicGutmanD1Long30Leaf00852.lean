/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00852 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 155030286085259390810520027136000000000000 59314149456706501054393650706485289680896 110276127592406609628741238784000000000000))
theorem leaf00852_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 155030286085259390810520027136000000000000 59314149456706501054393650706485289680896 110276127592406609628741238784000000000000 raw00852=true := by decide +kernel
#print axioms leaf00852_raw
theorem leaf00852_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00852=true := by decide +kernel
#print axioms leaf00852_rectangular
def affine00852 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00852 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00852_transform : affine00852=(NestedInteger.clearedAll 3 raw00852 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00852_transform
theorem leaf00852_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00852=true := by decide +kernel
#print axioms leaf00852_sign
theorem leaf00852_log : RationalLog.accepts (133564853/536870912) (-2987516069/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00852_log
def leaf00852 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (537869353519/1000000000000) (133564853/536870912) (-2987516069/4294967296) 3 8 ![60,0,4] ![(17/320),0,(1/8)] ![(1/640),1,(1/8)] affine00852
theorem leaf00852_checked : FastNestedCellData.accepts 1 2 4 leaf00852=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (537869353519/1000000000000) (133564853/536870912) (-2987516069/4294967296) 3 8 ![60,0,4] ![(17/320),0,(1/8)] ![(1/640),1,(1/8)] 155030286085259390810520027136000000000000 59314149456706501054393650706485289680896 110276127592406609628741238784000000000000 raw00852 affine00852
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00852_raw leaf00852_rectangular
    leaf00852_transform leaf00852_sign leaf00852_log
#print axioms leaf00852_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
