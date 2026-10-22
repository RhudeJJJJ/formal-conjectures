/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00912 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2999377754699599329736471347200000000000 1177078488983626016218981866077272670208 2010904651336810221816669798400000000000))
theorem leaf00912_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2999377754699599329736471347200000000000 1177078488983626016218981866077272670208 2010904651336810221816669798400000000000 raw00912=true := by decide +kernel
#print axioms leaf00912_raw
theorem leaf00912_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00912=true := by decide +kernel
#print axioms leaf00912_rectangular
def affine00912 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00912 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00912_transform : affine00912=(NestedInteger.clearedAll 3 raw00912 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00912_transform
theorem leaf00912_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00912=true := by decide +kernel
#print axioms leaf00912_sign
theorem leaf00912_log : RationalLog.accepts (265796703/1073741824) (-1499129523/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00912_log
def leaf00912 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (117069547599/200000000000) (265796703/1073741824) (-1499129523/2147483648) 3 8 ![60,0,4] ![(23/320),0,(1/8)] ![(1/320),1,(1/8)] affine00912
theorem leaf00912_checked : FastNestedCellData.accepts 1 2 4 leaf00912=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (117069547599/200000000000) (265796703/1073741824) (-1499129523/2147483648) 3 8 ![60,0,4] ![(23/320),0,(1/8)] ![(1/320),1,(1/8)] 2999377754699599329736471347200000000000 1177078488983626016218981866077272670208 2010904651336810221816669798400000000000 raw00912 affine00912
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00912_raw leaf00912_rectangular
    leaf00912_transform leaf00912_sign leaf00912_log
#print axioms leaf00912_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
