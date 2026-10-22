/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01306 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1158108862779268636308668416000000000000 1191417815817428454090449329883602485248 1186081261420618482621693820928000000000000))
theorem leaf01306_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1158108862779268636308668416000000000000 1191417815817428454090449329883602485248 1186081261420618482621693820928000000000000 raw01306=true := by decide +kernel
#print axioms leaf01306_raw
theorem leaf01306_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01306=true := by decide +kernel
#print axioms leaf01306_rectangular
def affine01306 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01306 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01306_transform : affine01306=(NestedInteger.clearedAll 3 raw01306 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01306_transform
theorem leaf01306_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01306=true := by decide +kernel
#print axioms leaf01306_sign
theorem leaf01306_log : RationalLog.accepts (4414063093/4294967296) (58737243/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01306_log
def leaf01306 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (251124829/250000000000) (4414063093/4294967296) (58737243/4294967296) 0 8 ![60,0,4] ![(1/8),0,(1/2)] ![(1/128),1,(1/4)] affine01306
theorem leaf01306_checked : FastNestedCellData.accepts 1 2 4 leaf01306=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (251124829/250000000000) (4414063093/4294967296) (58737243/4294967296) 0 8 ![60,0,4] ![(1/8),0,(1/2)] ![(1/128),1,(1/4)] 1158108862779268636308668416000000000000 1191417815817428454090449329883602485248 1186081261420618482621693820928000000000000 raw01306 affine01306
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01306_raw leaf01306_rectangular
    leaf01306_transform leaf01306_sign leaf01306_log
#print axioms leaf01306_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
