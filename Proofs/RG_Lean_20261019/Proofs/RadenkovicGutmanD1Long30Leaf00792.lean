/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00792 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2192747790511169742470117326848000000000000 884056545036836335469832986003520469598208 1859306950798559027086632157184000000000000))
theorem leaf00792_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2192747790511169742470117326848000000000000 884056545036836335469832986003520469598208 1859306950798559027086632157184000000000000 raw00792=true := by decide +kernel
#print axioms leaf00792_raw
theorem leaf00792_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00792=true := by decide +kernel
#print axioms leaf00792_rectangular
def affine00792 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00792 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00792_transform : affine00792=(NestedInteger.clearedAll 3 raw00792 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00792_transform
theorem leaf00792_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00792=true := by decide +kernel
#print axioms leaf00792_sign
theorem leaf00792_log : RationalLog.accepts (586798459/2147483648) (-2786082261/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00792_log
def leaf00792 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (475476383637/1000000000000) (586798459/2147483648) (-2786082261/4294967296) 2 8 ![60,0,4] ![(13/320),0,(1/8)] ![(3/3200),1,(1/8)] affine00792
theorem leaf00792_checked : FastNestedCellData.accepts 1 2 4 leaf00792=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (475476383637/1000000000000) (586798459/2147483648) (-2786082261/4294967296) 2 8 ![60,0,4] ![(13/320),0,(1/8)] ![(3/3200),1,(1/8)] 2192747790511169742470117326848000000000000 884056545036836335469832986003520469598208 1859306950798559027086632157184000000000000 raw00792 affine00792
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00792_raw leaf00792_rectangular
    leaf00792_transform leaf00792_sign leaf00792_log
#print axioms leaf00792_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
