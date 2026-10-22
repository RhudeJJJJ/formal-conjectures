/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01313 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000))
theorem leaf01313_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000 raw01313=true := by decide +kernel
#print axioms leaf01313_raw
theorem leaf01313_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01313=true := by decide +kernel
#print axioms leaf01313_rectangular
def affine01313 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01313 (IntegerComputedClassCell.leftNumerator ![(15/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/128),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01313_transform : affine01313=(NestedInteger.clearedAll 3 raw01313 (IntegerComputedClassCell.leftNumerator ![(15/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/128),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01313_transform
theorem leaf01313_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01313=true := by decide +kernel
#print axioms leaf01313_sign
theorem leaf01313_log : RationalLog.accepts (4400767117/4294967296) (52258863/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01313_log
def leaf01313 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (83881081/100000000000) (4400767117/4294967296) (52258863/4294967296) 0 8 ![60,0,4] ![(15/128),0,(7/8)] ![(1/128),1,(1/16)] affine01313
theorem leaf01313_checked : FastNestedCellData.accepts 1 2 4 leaf01313=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (83881081/100000000000) (4400767117/4294967296) (52258863/4294967296) 0 8 ![60,0,4] ![(15/128),0,(7/8)] ![(1/128),1,(1/16)] 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000 raw01313 affine01313
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01313_raw leaf01313_rectangular
    leaf01313_transform leaf01313_sign leaf01313_log
#print axioms leaf01313_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
