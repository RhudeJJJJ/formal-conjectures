/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00477 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 408195923907279415595237376000000000000 414003361828752370084653637025012908032 1169324216329799720973979615232000000000000))
theorem leaf00477_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 408195923907279415595237376000000000000 414003361828752370084653637025012908032 1169324216329799720973979615232000000000000 raw00477=true := by decide +kernel
#print axioms leaf00477_raw
theorem leaf00477_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00477=true := by decide +kernel
#print axioms leaf00477_rectangular
def affine00477 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00477 (IntegerComputedClassCell.leftNumerator ![(11/128),0,0] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,0] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/128),0,0] ![(1/128),1,(1/4)]))
theorem leaf00477_transform : affine00477=(NestedInteger.clearedAll 3 raw00477 (IntegerComputedClassCell.leftNumerator ![(11/128),0,0] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,0] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/128),0,0] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf00477_transform
theorem leaf00477_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00477=true := by decide +kernel
#print axioms leaf00477_sign
theorem leaf00477_log : RationalLog.accepts (2177265211/2147483648) (29576945/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00477_log
def leaf00477 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (177026763/500000000000) (2177265211/2147483648) (29576945/4294967296) 0 8 ![52,0,4] ![(11/128),0,0] ![(1/128),1,(1/4)] affine00477
theorem leaf00477_checked : FastNestedCellData.accepts 1 0 4 leaf00477=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (177026763/500000000000) (2177265211/2147483648) (29576945/4294967296) 0 8 ![52,0,4] ![(11/128),0,0] ![(1/128),1,(1/4)] 408195923907279415595237376000000000000 414003361828752370084653637025012908032 1169324216329799720973979615232000000000000 raw00477 affine00477
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00477_raw leaf00477_rectangular
    leaf00477_transform leaf00477_sign leaf00477_log
#print axioms leaf00477_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
