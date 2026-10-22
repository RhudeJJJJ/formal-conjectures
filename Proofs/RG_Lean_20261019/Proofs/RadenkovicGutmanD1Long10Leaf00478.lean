/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00478 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 408195923907279415595237376000000000000 414003361828752370084653637025012908032 1169324216329799720973979615232000000000000))
theorem leaf00478_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 408195923907279415595237376000000000000 414003361828752370084653637025012908032 1169324216329799720973979615232000000000000 raw00478=true := by decide +kernel
#print axioms leaf00478_raw
theorem leaf00478_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00478=true := by decide +kernel
#print axioms leaf00478_rectangular
def affine00478 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00478 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(1/4)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(1/4)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/128),0,(1/4)] ![(1/128),1,(1/4)]))
theorem leaf00478_transform : affine00478=(NestedInteger.clearedAll 3 raw00478 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(1/4)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(1/4)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/128),0,(1/4)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf00478_transform
theorem leaf00478_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00478=true := by decide +kernel
#print axioms leaf00478_sign
theorem leaf00478_log : RationalLog.accepts (2177265211/2147483648) (29576945/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00478_log
def leaf00478 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (177026763/500000000000) (2177265211/2147483648) (29576945/4294967296) 0 8 ![52,0,4] ![(11/128),0,(1/4)] ![(1/128),1,(1/4)] affine00478
theorem leaf00478_checked : FastNestedCellData.accepts 1 0 4 leaf00478=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (177026763/500000000000) (2177265211/2147483648) (29576945/4294967296) 0 8 ![52,0,4] ![(11/128),0,(1/4)] ![(1/128),1,(1/4)] 408195923907279415595237376000000000000 414003361828752370084653637025012908032 1169324216329799720973979615232000000000000 raw00478 affine00478
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00478_raw leaf00478_rectangular
    leaf00478_transform leaf00478_sign leaf00478_log
#print axioms leaf00478_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
