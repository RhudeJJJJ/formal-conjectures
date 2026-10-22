/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01312 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000))
theorem leaf01312_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000 raw01312=true := by decide +kernel
#print axioms leaf01312_raw
theorem leaf01312_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01312=true := by decide +kernel
#print axioms leaf01312_rectangular
def affine01312 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01312 (IntegerComputedClassCell.leftNumerator ![(15/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(15/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(15/128),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01312_transform : affine01312=(NestedInteger.clearedAll 3 raw01312 (IntegerComputedClassCell.leftNumerator ![(15/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(15/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(15/128),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01312_transform
theorem leaf01312_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01312=true := by decide +kernel
#print axioms leaf01312_sign
theorem leaf01312_log : RationalLog.accepts (4400767117/4294967296) (52258863/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01312_log
def leaf01312 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (83881081/100000000000) (4400767117/4294967296) (52258863/4294967296) 0 8 ![60,0,4] ![(15/128),0,(3/4)] ![(1/128),1,(1/8)] affine01312
theorem leaf01312_checked : FastNestedCellData.accepts 1 2 4 leaf01312=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (83881081/100000000000) (4400767117/4294967296) (52258863/4294967296) 0 8 ![60,0,4] ![(15/128),0,(3/4)] ![(1/128),1,(1/8)] 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000 raw01312 affine01312
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01312_raw leaf01312_rectangular
    leaf01312_transform leaf01312_sign leaf01312_log
#print axioms leaf01312_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
