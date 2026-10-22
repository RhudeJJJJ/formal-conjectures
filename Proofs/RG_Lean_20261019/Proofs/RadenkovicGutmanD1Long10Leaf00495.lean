/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00495 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 122695635902517565456384000000000000 122729261516583218402599159392632832 96103122580637072398120648704000000000000))
theorem leaf00495_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 122695635902517565456384000000000000 122729261516583218402599159392632832 96103122580637072398120648704000000000000 raw00495=true := by decide +kernel
#print axioms leaf00495_raw
theorem leaf00495_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00495=true := by decide +kernel
#print axioms leaf00495_rectangular
def affine00495 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00495 (IntegerComputedClassCell.leftNumerator ![(3/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(3/256),0,0] ![(1/256),1,1]))
theorem leaf00495_transform : affine00495=(NestedInteger.clearedAll 3 raw00495 (IntegerComputedClassCell.leftNumerator ![(3/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(3/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf00495_transform
theorem leaf00495_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00495=true := by decide +kernel
#print axioms leaf00495_sign
theorem leaf00495_log : RationalLog.accepts (1074034719/1073741824) (292855/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00495_log
def leaf00495 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (638529/500000000000) (1074034719/1073741824) (292855/2147483648) 0 8 ![52,0,4] ![(3/256),0,0] ![(1/256),1,1] affine00495
theorem leaf00495_checked : FastNestedCellData.accepts 1 0 4 leaf00495=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (638529/500000000000) (1074034719/1073741824) (292855/2147483648) 0 8 ![52,0,4] ![(3/256),0,0] ![(1/256),1,1] 122695635902517565456384000000000000 122729261516583218402599159392632832 96103122580637072398120648704000000000000 raw00495 affine00495
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00495_raw leaf00495_rectangular
    leaf00495_transform leaf00495_sign leaf00495_log
#print axioms leaf00495_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
