/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01105 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 38146288475134882689014405529600000000000 45283866895013317374766871116126800052224 218983271157492435763593635430400000000000))
theorem leaf01105_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 38146288475134882689014405529600000000000 45283866895013317374766871116126800052224 218983271157492435763593635430400000000000 raw01105=true := by decide +kernel
#print axioms leaf01105_raw
theorem leaf01105_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01105=true := by decide +kernel
#print axioms leaf01105_rectangular
def affine01105 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01105 (IntegerComputedClassCell.leftNumerator ![(9/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/16),0,0] ![(1/32),1,(1/2)]))
theorem leaf01105_transform : affine01105=(NestedInteger.clearedAll 3 raw01105 (IntegerComputedClassCell.leftNumerator ![(9/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/16),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf01105_transform
theorem leaf01105_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01105=true := by decide +kernel
#print axioms leaf01105_sign
theorem leaf01105_log : RationalLog.accepts (2112461777/2147483648) (-17655313/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01105_log
def leaf01105 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (41358288837/200000000000) (2112461777/2147483648) (-17655313/2147483648) 1 8 ![60,0,4] ![(9/16),0,0] ![(1/32),1,(1/2)] affine01105
theorem leaf01105_checked : FastNestedCellData.accepts 1 2 4 leaf01105=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (41358288837/200000000000) (2112461777/2147483648) (-17655313/2147483648) 1 8 ![60,0,4] ![(9/16),0,0] ![(1/32),1,(1/2)] 38146288475134882689014405529600000000000 45283866895013317374766871116126800052224 218983271157492435763593635430400000000000 raw01105 affine01105
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01105_raw leaf01105_rectangular
    leaf01105_transform leaf01105_sign leaf01105_log
#print axioms leaf01105_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
