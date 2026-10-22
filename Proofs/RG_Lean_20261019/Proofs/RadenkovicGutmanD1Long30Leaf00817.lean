/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00817 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9261089854341022120712001814528000000000000 3632692715403175016493118791041702328008704 7235795556832938939077506367488000000000000))
theorem leaf00817_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9261089854341022120712001814528000000000000 3632692715403175016493118791041702328008704 7235795556832938939077506367488000000000000 raw00817=true := by decide +kernel
#print axioms leaf00817_raw
theorem leaf00817_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00817=true := by decide +kernel
#print axioms leaf00817_rectangular
def affine00817 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00817 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00817_transform : affine00817=(NestedInteger.clearedAll 3 raw00817 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00817_transform
theorem leaf00817_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00817=true := by decide +kernel
#print axioms leaf00817_sign
theorem leaf00817_log : RationalLog.accepts (1121614391/4294967296) (-2883372405/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00817_log
def leaf00817 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (502044686983/1000000000000) (1121614391/4294967296) (-2883372405/4294967296) 2 8 ![60,0,4] ![(29/640),0,(1/8)] ![(3/3200),1,(1/8)] affine00817
theorem leaf00817_checked : FastNestedCellData.accepts 1 2 4 leaf00817=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (502044686983/1000000000000) (1121614391/4294967296) (-2883372405/4294967296) 2 8 ![60,0,4] ![(29/640),0,(1/8)] ![(3/3200),1,(1/8)] 9261089854341022120712001814528000000000000 3632692715403175016493118791041702328008704 7235795556832938939077506367488000000000000 raw00817 affine00817
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00817_raw leaf00817_rectangular
    leaf00817_transform leaf00817_sign leaf00817_log
#print axioms leaf00817_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
