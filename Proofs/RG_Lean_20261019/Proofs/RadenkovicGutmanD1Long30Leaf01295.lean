/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01295 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 100425569500005521774608384000000000000 104015856486284521992413205522383110144 74633705315414231148685950976000000000000))
theorem leaf01295_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 100425569500005521774608384000000000000 104015856486284521992413205522383110144 74633705315414231148685950976000000000000 raw01295=true := by decide +kernel
#print axioms leaf01295_raw
theorem leaf01295_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01295=true := by decide +kernel
#print axioms leaf01295_rectangular
def affine01295 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01295 (IntegerComputedClassCell.leftNumerator ![(9/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/64),0,0] ![(1/128),1,(1/2)]))
theorem leaf01295_transform : affine01295=(NestedInteger.clearedAll 3 raw01295 (IntegerComputedClassCell.leftNumerator ![(9/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/64),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01295_transform
theorem leaf01295_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01295=true := by decide +kernel
#print axioms leaf01295_sign
theorem leaf01295_log : RationalLog.accepts (2221162147/2147483648) (36221379/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01295_log
def leaf01295 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (174210593/125000000000) (2221162147/2147483648) (36221379/2147483648) 0 8 ![60,0,4] ![(9/64),0,0] ![(1/128),1,(1/2)] affine01295
theorem leaf01295_checked : FastNestedCellData.accepts 1 2 4 leaf01295=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (174210593/125000000000) (2221162147/2147483648) (36221379/2147483648) 0 8 ![60,0,4] ![(9/64),0,0] ![(1/128),1,(1/2)] 100425569500005521774608384000000000000 104015856486284521992413205522383110144 74633705315414231148685950976000000000000 raw01295 affine01295
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01295_raw leaf01295_rectangular
    leaf01295_transform leaf01295_sign leaf01295_log
#print axioms leaf01295_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
