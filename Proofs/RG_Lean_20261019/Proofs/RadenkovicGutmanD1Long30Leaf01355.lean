/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01355 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1448308295121954340549427200000000000 1448847872711772353271682065493917696 922680826992090064933034655744000000000000))
theorem leaf01355_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1448308295121954340549427200000000000 1448847872711772353271682065493917696 922680826992090064933034655744000000000000 raw01355=true := by decide +kernel
#print axioms leaf01355_raw
theorem leaf01355_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01355=true := by decide +kernel
#print axioms leaf01355_rectangular
def affine01355 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01355 (IntegerComputedClassCell.leftNumerator ![(7/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(7/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(7/512),0,0] ![(1/512),1,1]))
theorem leaf01355_transform : affine01355=(NestedInteger.clearedAll 3 raw01355 (IntegerComputedClassCell.leftNumerator ![(7/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(7/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(7/512),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf01355_transform
theorem leaf01355_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01355=true := by decide +kernel
#print axioms leaf01355_sign
theorem leaf01355_log : RationalLog.accepts (2148280335/2147483648) (796539/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01355_log
def leaf01355 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1570259/1000000000000) (2148280335/2147483648) (796539/4294967296) 0 8 ![60,0,4] ![(7/512),0,0] ![(1/512),1,1] affine01355
theorem leaf01355_checked : FastNestedCellData.accepts 1 2 4 leaf01355=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1570259/1000000000000) (2148280335/2147483648) (796539/4294967296) 0 8 ![60,0,4] ![(7/512),0,0] ![(1/512),1,1] 1448308295121954340549427200000000000 1448847872711772353271682065493917696 922680826992090064933034655744000000000000 raw01355 affine01355
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01355_raw leaf01355_rectangular
    leaf01355_transform leaf01355_sign leaf01355_log
#print axioms leaf01355_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
