/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00502 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3746778901860493810098321227776000000000000 2405507312793798617037783221842114768797696 11843180216614818084461620494336000000000000))
theorem leaf00502_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3746778901860493810098321227776000000000000 2405507312793798617037783221842114768797696 11843180216614818084461620494336000000000000 raw00502=true := by decide +kernel
#print axioms leaf00502_raw
theorem leaf00502_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00502=true := by decide +kernel
#print axioms leaf00502_rectangular
def affine00502 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00502 (IntegerComputedClassCell.leftNumerator ![(43/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(43/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(43/3200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00502_transform : affine00502=(NestedInteger.clearedAll 3 raw00502 (IntegerComputedClassCell.leftNumerator ![(43/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(43/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(43/3200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00502_transform
theorem leaf00502_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00502=true := by decide +kernel
#print axioms leaf00502_sign
theorem leaf00502_log : RationalLog.accepts (2291933181/4294967296) (-1348723481/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00502_log
def leaf00502 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (203113291261/1000000000000) (2291933181/4294967296) (-1348723481/4294967296) 1 8 ![60,0,4] ![(43/3200),0,(1/8)] ![(1/3200),1,(1/8)] affine00502
theorem leaf00502_checked : FastNestedCellData.accepts 1 2 4 leaf00502=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (203113291261/1000000000000) (2291933181/4294967296) (-1348723481/4294967296) 1 8 ![60,0,4] ![(43/3200),0,(1/8)] ![(1/3200),1,(1/8)] 3746778901860493810098321227776000000000000 2405507312793798617037783221842114768797696 11843180216614818084461620494336000000000000 raw00502 affine00502
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00502_raw leaf00502_rectangular
    leaf00502_transform leaf00502_sign leaf00502_log
#print axioms leaf00502_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
