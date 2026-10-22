/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00483 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 927395826642694840575328256000000000000 936317237094363803065972448561335369728 4656049754668854854062914404352000000000000))
theorem leaf00483_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 927395826642694840575328256000000000000 936317237094363803065972448561335369728 4656049754668854854062914404352000000000000 raw00483=true := by decide +kernel
#print axioms leaf00483_raw
theorem leaf00483_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00483=true := by decide +kernel
#print axioms leaf00483_rectangular
def affine00483 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00483 (IntegerComputedClassCell.leftNumerator ![(9/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/128),0,0] ![(1/128),1,(1/2)]))
theorem leaf00483_transform : affine00483=(NestedInteger.clearedAll 3 raw00483 (IntegerComputedClassCell.leftNumerator ![(9/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/128),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf00483_transform
theorem leaf00483_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00483=true := by decide +kernel
#print axioms leaf00483_sign
theorem leaf00483_log : RationalLog.accepts (4335412407/4294967296) (5031983/1073741824) 0 8=true := by decide +kernel
#print axioms leaf00483_log
def leaf00483 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (100548457/500000000000) (4335412407/4294967296) (5031983/1073741824) 0 8 ![52,0,4] ![(9/128),0,0] ![(1/128),1,(1/2)] affine00483
theorem leaf00483_checked : FastNestedCellData.accepts 1 0 4 leaf00483=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (100548457/500000000000) (4335412407/4294967296) (5031983/1073741824) 0 8 ![52,0,4] ![(9/128),0,0] ![(1/128),1,(1/2)] 927395826642694840575328256000000000000 936317237094363803065972448561335369728 4656049754668854854062914404352000000000000 raw00483 affine00483
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00483_raw leaf00483_rectangular
    leaf00483_transform leaf00483_sign leaf00483_log
#print axioms leaf00483_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
