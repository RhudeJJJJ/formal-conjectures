/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00432 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 20647642200052222511204532224000000000000 23652456697259715849002669123815902019584 1760938816409361943944377663488000000000000))
theorem leaf00432_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 20647642200052222511204532224000000000000 23652456697259715849002669123815902019584 1760938816409361943944377663488000000000000 raw00432=true := by decide +kernel
#print axioms leaf00432_raw
theorem leaf00432_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00432=true := by decide +kernel
#print axioms leaf00432_rectangular
def affine00432 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00432 (IntegerComputedClassCell.leftNumerator ![(5/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/16),0,0] ![(1/32),1,(1/2)]))
theorem leaf00432_transform : affine00432=(NestedInteger.clearedAll 3 raw00432 (IntegerComputedClassCell.leftNumerator ![(5/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/16),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf00432_transform
theorem leaf00432_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00432=true := by decide +kernel
#print axioms leaf00432_sign
theorem leaf00432_log : RationalLog.accepts (4854797877/4294967296) (32889659/536870912) 0 8=true := by decide +kernel
#print axioms leaf00432_log
def leaf00432 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (6715865559/500000000000) (4854797877/4294967296) (32889659/536870912) 0 8 ![52,0,4] ![(5/16),0,0] ![(1/32),1,(1/2)] affine00432
theorem leaf00432_checked : FastNestedCellData.accepts 1 0 4 leaf00432=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (6715865559/500000000000) (4854797877/4294967296) (32889659/536870912) 0 8 ![52,0,4] ![(5/16),0,0] ![(1/32),1,(1/2)] 20647642200052222511204532224000000000000 23652456697259715849002669123815902019584 1760938816409361943944377663488000000000000 raw00432 affine00432
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00432_raw leaf00432_rectangular
    leaf00432_transform leaf00432_sign leaf00432_log
#print axioms leaf00432_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
