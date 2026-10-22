/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01148 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 91147474388888696153261159219200000000000 116556507950919629318755228389590502998016 1179455649600540499198013865984000000000000))
theorem leaf01148_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 91147474388888696153261159219200000000000 116556507950919629318755228389590502998016 1179455649600540499198013865984000000000000 raw01148=true := by decide +kernel
#print axioms leaf01148_raw
theorem leaf01148_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01148=true := by decide +kernel
#print axioms leaf01148_rectangular
def affine01148 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01148 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01148_transform : affine01148=(NestedInteger.clearedAll 3 raw01148 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01148_transform
theorem leaf01148_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01148=true := by decide +kernel
#print axioms leaf01148_sign
theorem leaf01148_log : RationalLog.accepts (2499161335/2147483648) (325684039/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01148_log
def leaf01148 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (98822289749/1000000000000) (2499161335/2147483648) (325684039/4294967296) 0 8 ![60,0,4] ![(15/16),0,(7/8)] ![(1/16),1,(1/16)] affine01148
theorem leaf01148_checked : FastNestedCellData.accepts 1 2 4 leaf01148=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (98822289749/1000000000000) (2499161335/2147483648) (325684039/4294967296) 0 8 ![60,0,4] ![(15/16),0,(7/8)] ![(1/16),1,(1/16)] 91147474388888696153261159219200000000000 116556507950919629318755228389590502998016 1179455649600540499198013865984000000000000 raw01148 affine01148
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01148_raw leaf01148_rectangular
    leaf01148_transform leaf01148_sign leaf01148_log
#print axioms leaf01148_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
