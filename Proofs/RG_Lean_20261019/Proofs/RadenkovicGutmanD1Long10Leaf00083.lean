/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00083 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 596149239157368982893836107776000000000000 552029706260699329074011902580024596758528 17081546102230408743717645058048000000000000))
theorem leaf00083_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 596149239157368982893836107776000000000000 552029706260699329074011902580024596758528 17081546102230408743717645058048000000000000 raw00083=true := by decide +kernel
#print axioms leaf00083_raw
theorem leaf00083_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00083=true := by decide +kernel
#print axioms leaf00083_rectangular
def affine00083 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00083 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00083_transform : affine00083=(NestedInteger.clearedAll 3 raw00083 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00083_transform
theorem leaf00083_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00083=true := by decide +kernel
#print axioms leaf00083_sign
theorem leaf00083_log : RationalLog.accepts (3852601633/4294967296) (-233421355/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00083_log
def leaf00083 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (32317315011/1000000000000) (3852601633/4294967296) (-233421355/4294967296) 1 8 ![52,0,4] ![(7/800),0,(1/2)] ![(1/3200),1,(1/2)] affine00083
theorem leaf00083_checked : FastNestedCellData.accepts 1 0 4 leaf00083=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (32317315011/1000000000000) (3852601633/4294967296) (-233421355/4294967296) 1 8 ![52,0,4] ![(7/800),0,(1/2)] ![(1/3200),1,(1/2)] 596149239157368982893836107776000000000000 552029706260699329074011902580024596758528 17081546102230408743717645058048000000000000 raw00083 affine00083
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00083_raw leaf00083_rectangular
    leaf00083_transform leaf00083_sign leaf00083_log
#print axioms leaf00083_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
