/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01136 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 136723748361361900994641788928000000000000 173336007180241722795841956897857248165888 1461653974499012849598302519296000000000000))
theorem leaf01136_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 136723748361361900994641788928000000000000 173336007180241722795841956897857248165888 1461653974499012849598302519296000000000000 raw01136=true := by decide +kernel
#print axioms leaf01136_raw
theorem leaf01136_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01136=true := by decide +kernel
#print axioms leaf01136_rectangular
def affine01136 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01136 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01136_transform : affine01136=(NestedInteger.clearedAll 3 raw01136 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/8),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01136_transform
theorem leaf01136_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01136=true := by decide +kernel
#print axioms leaf01136_sign
theorem leaf01136_log : RationalLog.accepts (1216954043/1073741824) (268868111/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01136_log
def leaf01136 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (118588948003/1000000000000) (1216954043/1073741824) (268868111/4294967296) 0 8 ![60,0,4] ![(7/8),0,(1/2)] ![(1/16),1,(1/4)] affine01136
theorem leaf01136_checked : FastNestedCellData.accepts 1 2 4 leaf01136=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (118588948003/1000000000000) (1216954043/1073741824) (268868111/4294967296) 0 8 ![60,0,4] ![(7/8),0,(1/2)] ![(1/16),1,(1/4)] 136723748361361900994641788928000000000000 173336007180241722795841956897857248165888 1461653974499012849598302519296000000000000 raw01136 affine01136
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01136_raw leaf01136_rectangular
    leaf01136_transform leaf01136_sign leaf01136_log
#print axioms leaf01136_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
