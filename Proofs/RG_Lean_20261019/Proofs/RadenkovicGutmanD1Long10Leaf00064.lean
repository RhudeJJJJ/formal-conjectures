/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00064 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 61217103460367191399519485952000000000000 54021345362563555495210210189641240281088 1017401465533490445577611116544000000000000))
theorem leaf00064_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 61217103460367191399519485952000000000000 54021345362563555495210210189641240281088 1017401465533490445577611116544000000000000 raw00064=true := by decide +kernel
#print axioms leaf00064_raw
theorem leaf00064_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00064=true := by decide +kernel
#print axioms leaf00064_rectangular
def affine00064 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00064 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00064_transform : affine00064=(NestedInteger.clearedAll 3 raw00064 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00064_transform
theorem leaf00064_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00064=true := by decide +kernel
#print axioms leaf00064_sign
theorem leaf00064_log : RationalLog.accepts (3599017437/4294967296) (-379638781/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00064_log
def leaf00064 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (13274343313/250000000000) (3599017437/4294967296) (-379638781/4294967296) 1 8 ![52,0,4] ![(11/1600),0,(1/4)] ![(1/3200),1,(1/4)] affine00064
theorem leaf00064_checked : FastNestedCellData.accepts 1 0 4 leaf00064=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (13274343313/250000000000) (3599017437/4294967296) (-379638781/4294967296) 1 8 ![52,0,4] ![(11/1600),0,(1/4)] ![(1/3200),1,(1/4)] 61217103460367191399519485952000000000000 54021345362563555495210210189641240281088 1017401465533490445577611116544000000000000 raw00064 affine00064
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00064_raw leaf00064_rectangular
    leaf00064_transform leaf00064_sign leaf00064_log
#print axioms leaf00064_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
