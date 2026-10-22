/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01032 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 34874191880601974305527431168000000000000 26371718280882996129854948247901329948672 54489651730782080262412959744000000000000))
theorem leaf01032_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 34874191880601974305527431168000000000000 26371718280882996129854948247901329948672 54489651730782080262412959744000000000000 raw01032=true := by decide +kernel
#print axioms leaf01032_raw
theorem leaf01032_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01032=true := by decide +kernel
#print axioms leaf01032_rectangular
def affine01032 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01032 (IntegerComputedClassCell.leftNumerator ![(67/320),0,(1/8)] ![(3/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(67/320),0,(1/8)] ![(3/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(67/320),0,(1/8)] ![(3/320),1,(1/8)]))
theorem leaf01032_transform : affine01032=(NestedInteger.clearedAll 3 raw01032 (IntegerComputedClassCell.leftNumerator ![(67/320),0,(1/8)] ![(3/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(67/320),0,(1/8)] ![(3/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(67/320),0,(1/8)] ![(3/320),1,(1/8)])) := by decide +kernel
#print axioms leaf01032_transform
theorem leaf01032_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01032=true := by decide +kernel
#print axioms leaf01032_sign
theorem leaf01032_log : RationalLog.accepts (1094301709/2147483648) (-723895613/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01032_log
def leaf01032 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (60497079361/125000000000) (1094301709/2147483648) (-723895613/2147483648) 1 8 ![60,0,4] ![(67/320),0,(1/8)] ![(3/320),1,(1/8)] affine01032
theorem leaf01032_checked : FastNestedCellData.accepts 1 2 4 leaf01032=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (60497079361/125000000000) (1094301709/2147483648) (-723895613/2147483648) 1 8 ![60,0,4] ![(67/320),0,(1/8)] ![(3/320),1,(1/8)] 34874191880601974305527431168000000000000 26371718280882996129854948247901329948672 54489651730782080262412959744000000000000 raw01032 affine01032
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01032_raw leaf01032_rectangular
    leaf01032_transform leaf01032_sign leaf01032_log
#print axioms leaf01032_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
