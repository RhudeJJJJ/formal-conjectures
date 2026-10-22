/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00075 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 6991099212450010046437638799360000000000 4704108404985344297164486014167678976 24824560832212958845285171200000000000))
theorem leaf00075_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 6991099212450010046437638799360000000000 4704108404985344297164486014167678976 24824560832212958845285171200000000000 raw00075=true := by decide +kernel
#print axioms leaf00075_raw
theorem leaf00075_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00075=true := by decide +kernel
#print axioms leaf00075_rectangular
def affine00075 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00075 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/1600),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00075_transform : affine00075=(NestedInteger.clearedAll 3 raw00075 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/1600),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00075_transform
theorem leaf00075_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00075=true := by decide +kernel
#print axioms leaf00075_sign
theorem leaf00075_log : RationalLog.accepts (1214785/2147483648) (-8028888505/2147483648) 11 8=true := by decide +kernel
#print axioms leaf00075_log
def leaf00075 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (37898824771/200000000000) (1214785/2147483648) (-8028888505/2147483648) 11 8 ![52,0,4] ![(13/1600),0,0] ![(1/3200),1,(1/4)] affine00075
theorem leaf00075_checked : FastNestedCellData.accepts 1 0 4 leaf00075=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (37898824771/200000000000) (1214785/2147483648) (-8028888505/2147483648) 11 8 ![52,0,4] ![(13/1600),0,0] ![(1/3200),1,(1/4)] 6991099212450010046437638799360000000000 4704108404985344297164486014167678976 24824560832212958845285171200000000000 raw00075 affine00075
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00075_raw leaf00075_rectangular
    leaf00075_transform leaf00075_sign leaf00075_log
#print axioms leaf00075_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
