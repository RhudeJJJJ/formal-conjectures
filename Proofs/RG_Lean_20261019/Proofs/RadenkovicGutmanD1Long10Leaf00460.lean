/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00460 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 2356863864828830229712601088000000000000 2461553158412188041318096472098572599296 1204133006329759885839608840192000000000000))
theorem leaf00460_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 2356863864828830229712601088000000000000 2461553158412188041318096472098572599296 1204133006329759885839608840192000000000000 raw00460=true := by decide +kernel
#print axioms leaf00460_raw
theorem leaf00460_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00460=true := by decide +kernel
#print axioms leaf00460_rectangular
def affine00460 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00460 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf00460_transform : affine00460=(NestedInteger.clearedAll 3 raw00460 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00460_transform
theorem leaf00460_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00460=true := by decide +kernel
#print axioms leaf00460_sign
theorem leaf00460_log : RationalLog.accepts (2238296857/2147483648) (44472759/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00460_log
def leaf00460 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1022126769/500000000000) (2238296857/2147483648) (44472759/2147483648) 0 8 ![52,0,4] ![(5/32),0,(1/2)] ![(1/64),1,(1/4)] affine00460
theorem leaf00460_checked : FastNestedCellData.accepts 1 0 4 leaf00460=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1022126769/500000000000) (2238296857/2147483648) (44472759/2147483648) 0 8 ![52,0,4] ![(5/32),0,(1/2)] ![(1/64),1,(1/4)] 2356863864828830229712601088000000000000 2461553158412188041318096472098572599296 1204133006329759885839608840192000000000000 raw00460 affine00460
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00460_raw leaf00460_rectangular
    leaf00460_transform leaf00460_sign leaf00460_log
#print axioms leaf00460_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
