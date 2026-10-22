/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00384 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1398135206071844742725894144000000000000 1677524020381909704354039849473135345664 5403552188863777216634290176000000000000))
theorem leaf00384_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1398135206071844742725894144000000000000 1677524020381909704354039849473135345664 5403552188863777216634290176000000000000 raw00384=true := by decide +kernel
#print axioms leaf00384_raw
theorem leaf00384_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00384=true := by decide +kernel
#print axioms leaf00384_rectangular
def affine00384 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00384 (IntegerComputedClassCell.leftNumerator ![(37/80),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/80),0,0] ![(3/80),1,(1/4)]))
theorem leaf00384_transform : affine00384=(NestedInteger.clearedAll 3 raw00384 (IntegerComputedClassCell.leftNumerator ![(37/80),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/80),0,0] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00384_transform
theorem leaf00384_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00384=true := by decide +kernel
#print axioms leaf00384_sign
theorem leaf00384_log : RationalLog.accepts (491552073/536870912) (-189386183/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00384_log
def leaf00384 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (38806047433/125000000000) (491552073/536870912) (-189386183/4294967296) 1 8 ![52,0,4] ![(37/80),0,0] ![(3/80),1,(1/4)] affine00384
theorem leaf00384_checked : FastNestedCellData.accepts 1 0 4 leaf00384=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (38806047433/125000000000) (491552073/536870912) (-189386183/4294967296) 1 8 ![52,0,4] ![(37/80),0,0] ![(3/80),1,(1/4)] 1398135206071844742725894144000000000000 1677524020381909704354039849473135345664 5403552188863777216634290176000000000000 raw00384 affine00384
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00384_raw leaf00384_rectangular
    leaf00384_transform leaf00384_sign leaf00384_log
#print axioms leaf00384_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
