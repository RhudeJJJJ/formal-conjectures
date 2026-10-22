/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00353 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 21258352629622822355519248793600000000000 15472705297985784127015013049299407732736 41957189682784486547561381888000000000000))
theorem leaf00353_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 21258352629622822355519248793600000000000 15472705297985784127015013049299407732736 41957189682784486547561381888000000000000 raw00353=true := by decide +kernel
#print axioms leaf00353_raw
theorem leaf00353_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00353=true := by decide +kernel
#print axioms leaf00353_rectangular
def affine00353 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00353 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)]))
theorem leaf00353_transform : affine00353=(NestedInteger.clearedAll 3 raw00353 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)])) := by decide +kernel
#print axioms leaf00353_transform
theorem leaf00353_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00353=true := by decide +kernel
#print axioms leaf00353_sign
theorem leaf00353_log : RationalLog.accepts (2283835805/4294967296) (-84770247/268435456) 1 8=true := by decide +kernel
#print axioms leaf00353_log
def leaf00353 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (46096704209/125000000000) (2283835805/4294967296) (-84770247/268435456) 1 8 ![52,0,4] ![(7/40),0,(1/2)] ![(1/80),1,(1/2)] affine00353
theorem leaf00353_checked : FastNestedCellData.accepts 1 0 4 leaf00353=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (46096704209/125000000000) (2283835805/4294967296) (-84770247/268435456) 1 8 ![52,0,4] ![(7/40),0,(1/2)] ![(1/80),1,(1/2)] 21258352629622822355519248793600000000000 15472705297985784127015013049299407732736 41957189682784486547561381888000000000000 raw00353 affine00353
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00353_raw leaf00353_rectangular
    leaf00353_transform leaf00353_sign leaf00353_log
#print axioms leaf00353_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
