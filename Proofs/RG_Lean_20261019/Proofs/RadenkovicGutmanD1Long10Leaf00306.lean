/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00306 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 204143063930458199902864277504000000000000 37782921586922519815056829483549244522496 53345852126619761527285088256000000000000))
theorem leaf00306_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 204143063930458199902864277504000000000000 37782921586922519815056829483549244522496 53345852126619761527285088256000000000000 raw00306=true := by decide +kernel
#print axioms leaf00306_raw
theorem leaf00306_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00306=true := by decide +kernel
#print axioms leaf00306_rectangular
def affine00306 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00306 (IntegerComputedClassCell.leftNumerator ![(7/80),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/80),0,0] ![(1/320),1,(1/4)]))
theorem leaf00306_transform : affine00306=(NestedInteger.clearedAll 3 raw00306 (IntegerComputedClassCell.leftNumerator ![(7/80),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/80),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00306_transform
theorem leaf00306_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00306=true := by decide +kernel
#print axioms leaf00306_sign
theorem leaf00306_log : RationalLog.accepts (232667597/2147483648) (-4772656335/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00306_log
def leaf00306 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (177065882729/250000000000) (232667597/2147483648) (-4772656335/4294967296) 4 8 ![52,0,4] ![(7/80),0,0] ![(1/320),1,(1/4)] affine00306
theorem leaf00306_checked : FastNestedCellData.accepts 1 0 4 leaf00306=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (177065882729/250000000000) (232667597/2147483648) (-4772656335/4294967296) 4 8 ![52,0,4] ![(7/80),0,0] ![(1/320),1,(1/4)] 204143063930458199902864277504000000000000 37782921586922519815056829483549244522496 53345852126619761527285088256000000000000 raw00306 affine00306
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00306_raw leaf00306_rectangular
    leaf00306_transform leaf00306_sign leaf00306_log
#print axioms leaf00306_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
