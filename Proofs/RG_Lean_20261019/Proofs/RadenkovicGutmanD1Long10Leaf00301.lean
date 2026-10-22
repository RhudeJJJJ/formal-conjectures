/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00301 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 460033122671402358298116096000000000000 235047662373910424457567454358346399744 541424218752623682128969728000000000000))
theorem leaf00301_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 460033122671402358298116096000000000000 235047662373910424457567454358346399744 541424218752623682128969728000000000000 raw00301=true := by decide +kernel
#print axioms leaf00301_raw
theorem leaf00301_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00301=true := by decide +kernel
#print axioms leaf00301_rectangular
def affine00301 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00301 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00301_transform : affine00301=(NestedInteger.clearedAll 3 raw00301 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00301_transform
theorem leaf00301_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00301=true := by decide +kernel
#print axioms leaf00301_sign
theorem leaf00301_log : RationalLog.accepts (191270791/536870912) (-277043519/536870912) 2 8=true := by decide +kernel
#print axioms leaf00301_log
def leaf00301 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (108532115037/250000000000) (191270791/536870912) (-277043519/536870912) 2 8 ![52,0,4] ![(13/160),0,(1/4)] ![(1/320),1,(1/4)] affine00301
theorem leaf00301_checked : FastNestedCellData.accepts 1 0 4 leaf00301=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (108532115037/250000000000) (191270791/536870912) (-277043519/536870912) 2 8 ![52,0,4] ![(13/160),0,(1/4)] ![(1/320),1,(1/4)] 460033122671402358298116096000000000000 235047662373910424457567454358346399744 541424218752623682128969728000000000000 raw00301 affine00301
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00301_raw leaf00301_rectangular
    leaf00301_transform leaf00301_sign leaf00301_log
#print axioms leaf00301_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
