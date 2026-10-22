/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00489 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 80855196774817421647151104000000000000 81099200559807141676671714142910939136 2055823602608755387221531426816000000000000))
theorem leaf00489_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 80855196774817421647151104000000000000 81099200559807141676671714142910939136 2055823602608755387221531426816000000000000 raw00489=true := by decide +kernel
#print axioms leaf00489_raw
theorem leaf00489_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00489=true := by decide +kernel
#print axioms leaf00489_rectangular
def affine00489 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00489 (IntegerComputedClassCell.leftNumerator ![(5/128),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/128),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.denominator ![(5/128),0,0] ![(1/128),1,1]))
theorem leaf00489_transform : affine00489=(NestedInteger.clearedAll 3 raw00489 (IntegerComputedClassCell.leftNumerator ![(5/128),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/128),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.denominator ![(5/128),0,0] ![(1/128),1,1])) := by decide +kernel
#print axioms leaf00489_transform
theorem leaf00489_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00489=true := by decide +kernel
#print axioms leaf00489_sign
theorem leaf00489_log : RationalLog.accepts (4307758659/4294967296) (12473/8388608) 0 8=true := by decide +kernel
#print axioms leaf00489_log
def leaf00489 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (39448521/1000000000000) (4307758659/4294967296) (12473/8388608) 0 8 ![52,0,4] ![(5/128),0,0] ![(1/128),1,1] affine00489
theorem leaf00489_checked : FastNestedCellData.accepts 1 0 4 leaf00489=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (39448521/1000000000000) (4307758659/4294967296) (12473/8388608) 0 8 ![52,0,4] ![(5/128),0,0] ![(1/128),1,1] 80855196774817421647151104000000000000 81099200559807141676671714142910939136 2055823602608755387221531426816000000000000 raw00489 affine00489
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00489_raw leaf00489_rectangular
    leaf00489_transform leaf00489_sign leaf00489_log
#print axioms leaf00489_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
