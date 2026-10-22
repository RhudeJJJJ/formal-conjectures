/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00088 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 82733944165472768730754711552000000000000 70126749845523442336298310618688851542016 977236595699859488030859460608000000000000))
theorem leaf00088_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 82733944165472768730754711552000000000000 70126749845523442336298310618688851542016 977236595699859488030859460608000000000000 raw00088=true := by decide +kernel
#print axioms leaf00088_raw
theorem leaf00088_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00088=true := by decide +kernel
#print axioms leaf00088_rectangular
def affine00088 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00088 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00088_transform : affine00088=(NestedInteger.clearedAll 3 raw00088 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00088_transform
theorem leaf00088_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00088=true := by decide +kernel
#print axioms leaf00088_sign
theorem leaf00088_log : RationalLog.accepts (1698369567/2147483648) (-125964983/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00088_log
def leaf00088 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (35880128801/500000000000) (1698369567/2147483648) (-125964983/1073741824) 1 8 ![52,0,4] ![(3/320),0,(1/4)] ![(1/3200),1,(1/4)] affine00088
theorem leaf00088_checked : FastNestedCellData.accepts 1 0 4 leaf00088=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (35880128801/500000000000) (1698369567/2147483648) (-125964983/1073741824) 1 8 ![52,0,4] ![(3/320),0,(1/4)] ![(1/3200),1,(1/4)] 82733944165472768730754711552000000000000 70126749845523442336298310618688851542016 977236595699859488030859460608000000000000 raw00088 affine00088
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00088_raw leaf00088_rectangular
    leaf00088_transform leaf00088_sign leaf00088_log
#print axioms leaf00088_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
