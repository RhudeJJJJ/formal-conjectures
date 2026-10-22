/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01152 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 404249960850461062865092608000000000000 517970569257465002066506429450854334464 5770518957600395033646727168000000000000))
theorem leaf01152_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 404249960850461062865092608000000000000 517970569257465002066506429450854334464 5770518957600395033646727168000000000000 raw01152=true := by decide +kernel
#print axioms leaf01152_raw
theorem leaf01152_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01152=true := by decide +kernel
#print axioms leaf01152_rectangular
def affine01152 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01152 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01152_transform : affine01152=(NestedInteger.clearedAll 3 raw01152 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01152_transform
theorem leaf01152_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01152=true := by decide +kernel
#print axioms leaf01152_sign
theorem leaf01152_log : RationalLog.accepts (2524954133/2147483648) (347733731/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01152_log
def leaf01152 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2805047589/31250000000) (2524954133/2147483648) (347733731/4294967296) 0 8 ![60,0,4] ![(7/8),0,(3/4)] ![(1/16),1,(1/8)] affine01152
theorem leaf01152_checked : FastNestedCellData.accepts 1 2 4 leaf01152=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2805047589/31250000000) (2524954133/2147483648) (347733731/4294967296) 0 8 ![60,0,4] ![(7/8),0,(3/4)] ![(1/16),1,(1/8)] 404249960850461062865092608000000000000 517970569257465002066506429450854334464 5770518957600395033646727168000000000000 raw01152 affine01152
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01152_raw leaf01152_rectangular
    leaf01152_transform leaf01152_sign leaf01152_log
#print axioms leaf01152_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
