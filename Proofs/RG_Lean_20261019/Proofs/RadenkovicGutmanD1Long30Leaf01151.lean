/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01151 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 25900128572768965764954718208000000000000 33195488034547311017794896832832905150464 369417007944772328947137380352000000000000))
theorem leaf01151_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 25900128572768965764954718208000000000000 33195488034547311017794896832832905150464 369417007944772328947137380352000000000000 raw01151=true := by decide +kernel
#print axioms leaf01151_raw
theorem leaf01151_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01151=true := by decide +kernel
#print axioms leaf01151_rectangular
def affine01151 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01151 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01151_transform : affine01151=(NestedInteger.clearedAll 3 raw01151 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01151_transform
theorem leaf01151_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01151=true := by decide +kernel
#print axioms leaf01151_sign
theorem leaf01151_log : RationalLog.accepts (2525437587/2147483648) (348144871/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01151_log
def leaf01151 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (22464780533/250000000000) (2525437587/2147483648) (348144871/4294967296) 0 8 ![60,0,4] ![(7/8),0,(1/2)] ![(1/16),1,(1/4)] affine01151
theorem leaf01151_checked : FastNestedCellData.accepts 1 2 4 leaf01151=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (22464780533/250000000000) (2525437587/2147483648) (348144871/4294967296) 0 8 ![60,0,4] ![(7/8),0,(1/2)] ![(1/16),1,(1/4)] 25900128572768965764954718208000000000000 33195488034547311017794896832832905150464 369417007944772328947137380352000000000000 raw01151 affine01151
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01151_raw leaf01151_rectangular
    leaf01151_transform leaf01151_sign leaf01151_log
#print axioms leaf01151_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
