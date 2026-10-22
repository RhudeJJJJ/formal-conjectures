/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00024 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1230156266669749558488969773056000000000000 37222224482088563639510317231251652608 558163923949336493385842688000000000000))
theorem leaf00024_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1230156266669749558488969773056000000000000 37222224482088563639510317231251652608 558163923949336493385842688000000000000 raw00024=true := by decide +kernel
#print axioms leaf00024_raw
theorem leaf00024_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00024=true := by decide +kernel
#print axioms leaf00024_rectangular
def affine00024 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00024 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/4000),0,0] ![(3/16000),1,(1/4)]))
theorem leaf00024_transform : affine00024=(NestedInteger.clearedAll 3 raw00024 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/4000),0,0] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00024_transform
theorem leaf00024_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00024=true := by decide +kernel
#print axioms leaf00024_sign
theorem leaf00024_log : RationalLog.accepts (121833/4294967296) (-5621201393/1073741824) 16 8=true := by decide +kernel
#print axioms leaf00024_log
def leaf00024 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (66686904841/1000000000000) (121833/4294967296) (-5621201393/1073741824) 16 8 ![52,0,4] ![(11/4000),0,0] ![(3/16000),1,(1/4)] affine00024
theorem leaf00024_checked : FastNestedCellData.accepts 1 0 4 leaf00024=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (66686904841/1000000000000) (121833/4294967296) (-5621201393/1073741824) 16 8 ![52,0,4] ![(11/4000),0,0] ![(3/16000),1,(1/4)] 1230156266669749558488969773056000000000000 37222224482088563639510317231251652608 558163923949336493385842688000000000000 raw00024 affine00024
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00024_raw leaf00024_rectangular
    leaf00024_transform leaf00024_sign leaf00024_log
#print axioms leaf00024_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
