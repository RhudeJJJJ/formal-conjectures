/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01042 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 512681924601964966705740382208000000000000 420849536839086648631909919867500329172992 946408402446249989574884327424000000000000))
theorem leaf01042_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 512681924601964966705740382208000000000000 420849536839086648631909919867500329172992 946408402446249989574884327424000000000000 raw01042=true := by decide +kernel
#print axioms leaf01042_raw
theorem leaf01042_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01042=true := by decide +kernel
#print axioms leaf01042_rectangular
def affine01042 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01042 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/8)] ![(3/160),1,(1/8)]))
theorem leaf01042_transform : affine01042=(NestedInteger.clearedAll 3 raw01042 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/8)] ![(3/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01042_transform
theorem leaf01042_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01042=true := by decide +kernel
#print axioms leaf01042_sign
theorem leaf01042_log : RationalLog.accepts (1220216369/2147483648) (-1213905037/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01042_log
def leaf01042 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (222340342579/500000000000) (1220216369/2147483648) (-1213905037/4294967296) 1 8 ![60,0,4] ![(19/80),0,(1/8)] ![(3/160),1,(1/8)] affine01042
theorem leaf01042_checked : FastNestedCellData.accepts 1 2 4 leaf01042=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (222340342579/500000000000) (1220216369/2147483648) (-1213905037/4294967296) 1 8 ![60,0,4] ![(19/80),0,(1/8)] ![(3/160),1,(1/8)] 512681924601964966705740382208000000000000 420849536839086648631909919867500329172992 946408402446249989574884327424000000000000 raw01042 affine01042
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01042_raw leaf01042_rectangular
    leaf01042_transform leaf01042_sign leaf01042_log
#print axioms leaf01042_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
