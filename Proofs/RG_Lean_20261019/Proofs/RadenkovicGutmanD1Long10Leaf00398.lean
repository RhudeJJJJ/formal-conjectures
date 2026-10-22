/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00398 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 897565827505303882505601941504000000000000 1189960560440504647300780219215360313786368 6114007809673509404556203655168000000000000))
theorem leaf00398_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 897565827505303882505601941504000000000000 1189960560440504647300780219215360313786368 6114007809673509404556203655168000000000000 raw00398=true := by decide +kernel
#print axioms leaf00398_raw
theorem leaf00398_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00398=true := by decide +kernel
#print axioms leaf00398_rectangular
def affine00398 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00398 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/16),0,(3/4)] ![(1/16),1,(1/4)]))
theorem leaf00398_transform : affine00398=(NestedInteger.clearedAll 3 raw00398 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/16),0,(3/4)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00398_transform
theorem leaf00398_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00398=true := by decide +kernel
#print axioms leaf00398_sign
theorem leaf00398_log : RationalLog.accepts (4766430057/4294967296) (111834149/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00398_log
def leaf00398 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (97314282013/500000000000) (4766430057/4294967296) (111834149/2147483648) 0 8 ![52,0,4] ![(11/16),0,(3/4)] ![(1/16),1,(1/4)] affine00398
theorem leaf00398_checked : FastNestedCellData.accepts 1 0 4 leaf00398=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (97314282013/500000000000) (4766430057/4294967296) (111834149/2147483648) 0 8 ![52,0,4] ![(11/16),0,(3/4)] ![(1/16),1,(1/4)] 897565827505303882505601941504000000000000 1189960560440504647300780219215360313786368 6114007809673509404556203655168000000000000 raw00398 affine00398
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00398_raw leaf00398_rectangular
    leaf00398_transform leaf00398_sign leaf00398_log
#print axioms leaf00398_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
