/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01230 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 2275535286266441392793321472000000000000 2515549017594647909249493107446263054336 318631683694522872564990083072000000000000))
theorem leaf01230_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 2275535286266441392793321472000000000000 2515549017594647909249493107446263054336 318631683694522872564990083072000000000000 raw01230=true := by decide +kernel
#print axioms leaf01230_raw
theorem leaf01230_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01230=true := by decide +kernel
#print axioms leaf01230_rectangular
def affine01230 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01230 (IntegerComputedClassCell.leftNumerator ![(17/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf01230_transform : affine01230=(NestedInteger.clearedAll 3 raw01230 (IntegerComputedClassCell.leftNumerator ![(17/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf01230_transform
theorem leaf01230_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01230=true := by decide +kernel
#print axioms leaf01230_sign
theorem leaf01230_log : RationalLog.accepts (588848887/536870912) (198453073/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01230_log
def leaf01230 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (7894848963/1000000000000) (588848887/536870912) (198453073/4294967296) 0 8 ![60,0,4] ![(17/64),0,0] ![(1/64),1,(1/2)] affine01230
theorem leaf01230_checked : FastNestedCellData.accepts 1 2 4 leaf01230=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (7894848963/1000000000000) (588848887/536870912) (198453073/4294967296) 0 8 ![60,0,4] ![(17/64),0,0] ![(1/64),1,(1/2)] 2275535286266441392793321472000000000000 2515549017594647909249493107446263054336 318631683694522872564990083072000000000000 raw01230 affine01230
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01230_raw leaf01230_rectangular
    leaf01230_transform leaf01230_sign leaf01230_log
#print axioms leaf01230_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
