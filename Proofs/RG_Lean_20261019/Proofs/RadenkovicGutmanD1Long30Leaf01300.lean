/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01300 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 54844152925542119809797324800000000000 56609241367619033588050145789475815424 47601071947133086613682467635200000000000))
theorem leaf01300_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 54844152925542119809797324800000000000 56609241367619033588050145789475815424 47601071947133086613682467635200000000000 raw01300=true := by decide +kernel
#print axioms leaf01300_raw
theorem leaf01300_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01300=true := by decide +kernel
#print axioms leaf01300_rectangular
def affine01300 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01300 (IntegerComputedClassCell.leftNumerator ![(17/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/128),0,0] ![(1/128),1,(1/2)]))
theorem leaf01300_transform : affine01300=(NestedInteger.clearedAll 3 raw01300 (IntegerComputedClassCell.leftNumerator ![(17/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/128),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01300_transform
theorem leaf01300_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01300=true := by decide +kernel
#print axioms leaf01300_sign
theorem leaf01300_log : RationalLog.accepts (1106982351/1073741824) (32736381/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01300_log
def leaf01300 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (237848599/200000000000) (1106982351/1073741824) (32736381/2147483648) 0 8 ![60,0,4] ![(17/128),0,0] ![(1/128),1,(1/2)] affine01300
theorem leaf01300_checked : FastNestedCellData.accepts 1 2 4 leaf01300=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (237848599/200000000000) (1106982351/1073741824) (32736381/2147483648) 0 8 ![60,0,4] ![(17/128),0,0] ![(1/128),1,(1/2)] 54844152925542119809797324800000000000 56609241367619033588050145789475815424 47601071947133086613682467635200000000000 raw01300 affine01300
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01300_raw leaf01300_rectangular
    leaf01300_transform leaf01300_sign leaf01300_log
#print axioms leaf01300_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
