/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01301 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 54844152925542119809797324800000000000 56609241367619033588050145789475815424 47601071947133086613682467635200000000000))
theorem leaf01301_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 54844152925542119809797324800000000000 56609241367619033588050145789475815424 47601071947133086613682467635200000000000 raw01301=true := by decide +kernel
#print axioms leaf01301_raw
theorem leaf01301_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01301=true := by decide +kernel
#print axioms leaf01301_rectangular
def affine01301 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01301 (IntegerComputedClassCell.leftNumerator ![(17/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01301_transform : affine01301=(NestedInteger.clearedAll 3 raw01301 (IntegerComputedClassCell.leftNumerator ![(17/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01301_transform
theorem leaf01301_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01301=true := by decide +kernel
#print axioms leaf01301_sign
theorem leaf01301_log : RationalLog.accepts (1106982351/1073741824) (32736381/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01301_log
def leaf01301 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (237848599/200000000000) (1106982351/1073741824) (32736381/2147483648) 0 8 ![60,0,4] ![(17/128),0,(1/2)] ![(1/128),1,(1/4)] affine01301
theorem leaf01301_checked : FastNestedCellData.accepts 1 2 4 leaf01301=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (237848599/200000000000) (1106982351/1073741824) (32736381/2147483648) 0 8 ![60,0,4] ![(17/128),0,(1/2)] ![(1/128),1,(1/4)] 54844152925542119809797324800000000000 56609241367619033588050145789475815424 47601071947133086613682467635200000000000 raw01301 affine01301
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01301_raw leaf01301_rectangular
    leaf01301_transform leaf01301_sign leaf01301_log
#print axioms leaf01301_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
