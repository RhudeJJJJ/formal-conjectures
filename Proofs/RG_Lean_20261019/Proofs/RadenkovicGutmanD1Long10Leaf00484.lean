/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00484 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 927395826642694840575328256000000000000 936317237094363803065972448561335369728 4656049754668854854062914404352000000000000))
theorem leaf00484_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 927395826642694840575328256000000000000 936317237094363803065972448561335369728 4656049754668854854062914404352000000000000 raw00484=true := by decide +kernel
#print axioms leaf00484_raw
theorem leaf00484_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00484=true := by decide +kernel
#print axioms leaf00484_rectangular
def affine00484 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00484 (IntegerComputedClassCell.leftNumerator ![(9/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf00484_transform : affine00484=(NestedInteger.clearedAll 3 raw00484 (IntegerComputedClassCell.leftNumerator ![(9/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf00484_transform
theorem leaf00484_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00484=true := by decide +kernel
#print axioms leaf00484_sign
theorem leaf00484_log : RationalLog.accepts (4335412407/4294967296) (5031983/1073741824) 0 8=true := by decide +kernel
#print axioms leaf00484_log
def leaf00484 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (100548457/500000000000) (4335412407/4294967296) (5031983/1073741824) 0 8 ![52,0,4] ![(9/128),0,(1/2)] ![(1/128),1,(1/4)] affine00484
theorem leaf00484_checked : FastNestedCellData.accepts 1 0 4 leaf00484=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (100548457/500000000000) (4335412407/4294967296) (5031983/1073741824) 0 8 ![52,0,4] ![(9/128),0,(1/2)] ![(1/128),1,(1/4)] 927395826642694840575328256000000000000 936317237094363803065972448561335369728 4656049754668854854062914404352000000000000 raw00484 affine00484
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00484_raw leaf00484_rectangular
    leaf00484_transform leaf00484_sign leaf00484_log
#print axioms leaf00484_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
