/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01241 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 553971166764130539136876544000000000000 602049797290469137156149466566305513472 104415205427095690927117697024000000000000))
theorem leaf01241_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 553971166764130539136876544000000000000 602049797290469137156149466566305513472 104415205427095690927117697024000000000000 raw01241=true := by decide +kernel
#print axioms leaf01241_raw
theorem leaf01241_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01241=true := by decide +kernel
#print axioms leaf01241_rectangular
def affine01241 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01241 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf01241_transform : affine01241=(NestedInteger.clearedAll 3 raw01241 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf01241_transform
theorem leaf01241_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01241=true := by decide +kernel
#print axioms leaf01241_sign
theorem leaf01241_log : RationalLog.accepts (4640963991/4294967296) (83191541/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01241_log
def leaf01241 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (720740091/125000000000) (4640963991/4294967296) (83191541/2147483648) 0 8 ![60,0,4] ![(15/64),0,(1/2)] ![(1/64),1,(1/4)] affine01241
theorem leaf01241_checked : FastNestedCellData.accepts 1 2 4 leaf01241=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (720740091/125000000000) (4640963991/4294967296) (83191541/2147483648) 0 8 ![60,0,4] ![(15/64),0,(1/2)] ![(1/64),1,(1/4)] 553971166764130539136876544000000000000 602049797290469137156149466566305513472 104415205427095690927117697024000000000000 raw01241 affine01241
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01241_raw leaf01241_rectangular
    leaf01241_transform leaf01241_sign leaf01241_log
#print axioms leaf01241_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
