/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01342 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 413695228051202550490202112000000000000 416113789044019658828781487457795309568 4638647035038167005989915590656000000000000))
theorem leaf01342_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 413695228051202550490202112000000000000 416113789044019658828781487457795309568 4638647035038167005989915590656000000000000 raw01342=true := by decide +kernel
#print axioms leaf01342_raw
theorem leaf01342_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01342=true := by decide +kernel
#print axioms leaf01342_rectangular
def affine01342 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01342 (IntegerComputedClassCell.leftNumerator ![(7/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(7/128),0,0] ![(1/256),1,1]))
theorem leaf01342_transform : affine01342=(NestedInteger.clearedAll 3 raw01342 (IntegerComputedClassCell.leftNumerator ![(7/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(7/128),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01342_transform
theorem leaf01342_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01342=true := by decide +kernel
#print axioms leaf01342_sign
theorem leaf01342_log : RationalLog.accepts (2159844599/2147483648) (1540689/536870912) 0 8=true := by decide +kernel
#print axioms leaf01342_log
def leaf01342 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (89705853/1000000000000) (2159844599/2147483648) (1540689/536870912) 0 8 ![60,0,4] ![(7/128),0,0] ![(1/256),1,1] affine01342
theorem leaf01342_checked : FastNestedCellData.accepts 1 2 4 leaf01342=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (89705853/1000000000000) (2159844599/2147483648) (1540689/536870912) 0 8 ![60,0,4] ![(7/128),0,0] ![(1/256),1,1] 413695228051202550490202112000000000000 416113789044019658828781487457795309568 4638647035038167005989915590656000000000000 raw01342 affine01342
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01342_raw leaf01342_rectangular
    leaf01342_transform leaf01342_sign leaf01342_log
#print axioms leaf01342_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
