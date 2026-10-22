/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00057 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2734074083198382404367959457792000000000000 882181665193271635357452516924365733888 5952062346936201481786753024000000000000))
theorem leaf00057_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2734074083198382404367959457792000000000000 882181665193271635357452516924365733888 5952062346936201481786753024000000000000 raw00057=true := by decide +kernel
#print axioms leaf00057_raw
theorem leaf00057_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00057=true := by decide +kernel
#print axioms leaf00057_rectangular
def affine00057 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00057 (IntegerComputedClassCell.leftNumerator ![(1/160),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/160),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00057_transform : affine00057=(NestedInteger.clearedAll 3 raw00057 (IntegerComputedClassCell.leftNumerator ![(1/160),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/160),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00057_transform
theorem leaf00057_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00057=true := by decide +kernel
#print axioms leaf00057_sign
theorem leaf00057_log : RationalLog.accepts (1206937/4294967296) (-8780108949/2147483648) 12 8=true := by decide +kernel
#print axioms leaf00057_log
def leaf00057 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (148214453037/1000000000000) (1206937/4294967296) (-8780108949/2147483648) 12 8 ![52,0,4] ![(1/160),0,0] ![(1/3200),1,(1/4)] affine00057
theorem leaf00057_checked : FastNestedCellData.accepts 1 0 4 leaf00057=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (148214453037/1000000000000) (1206937/4294967296) (-8780108949/2147483648) 12 8 ![52,0,4] ![(1/160),0,0] ![(1/3200),1,(1/4)] 2734074083198382404367959457792000000000000 882181665193271635357452516924365733888 5952062346936201481786753024000000000000 raw00057 affine00057
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00057_raw leaf00057_rectangular
    leaf00057_transform leaf00057_sign leaf00057_log
#print axioms leaf00057_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
