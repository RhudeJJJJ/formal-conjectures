/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00991 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 118135523638892580506217060761600000000000 61051537927890354188560956098885455970304 95331366956534742400316630630400000000000))
theorem leaf00991_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 118135523638892580506217060761600000000000 61051537927890354188560956098885455970304 95331366956534742400316630630400000000000 raw00991=true := by decide +kernel
#print axioms leaf00991_raw
theorem leaf00991_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00991=true := by decide +kernel
#print axioms leaf00991_rectangular
def affine00991 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00991 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/16)] ![(1/160),1,(1/16)]))
theorem leaf00991_transform : affine00991=(NestedInteger.clearedAll 3 raw00991 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/16)] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00991_transform
theorem leaf00991_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00991=true := by decide +kernel
#print axioms leaf00991_sign
theorem leaf00991_log : RationalLog.accepts (676538487/2147483648) (-19378737/33554432) 2 8=true := by decide +kernel
#print axioms leaf00991_log
def leaf00991 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (128082791377/200000000000) (676538487/2147483648) (-19378737/33554432) 2 8 ![60,0,4] ![(11/80),0,(1/16)] ![(1/160),1,(1/16)] affine00991
theorem leaf00991_checked : FastNestedCellData.accepts 1 2 4 leaf00991=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (128082791377/200000000000) (676538487/2147483648) (-19378737/33554432) 2 8 ![60,0,4] ![(11/80),0,(1/16)] ![(1/160),1,(1/16)] 118135523638892580506217060761600000000000 61051537927890354188560956098885455970304 95331366956534742400316630630400000000000 raw00991 affine00991
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00991_raw leaf00991_rectangular
    leaf00991_transform leaf00991_sign leaf00991_log
#print axioms leaf00991_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
