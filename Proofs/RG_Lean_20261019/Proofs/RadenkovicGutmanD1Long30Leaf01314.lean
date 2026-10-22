/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01314 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000))
theorem leaf01314_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000 raw01314=true := by decide +kernel
#print axioms leaf01314_raw
theorem leaf01314_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01314=true := by decide +kernel
#print axioms leaf01314_rectangular
def affine01314 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01314 (IntegerComputedClassCell.leftNumerator ![(15/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/128),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01314_transform : affine01314=(NestedInteger.clearedAll 3 raw01314 (IntegerComputedClassCell.leftNumerator ![(15/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/128),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01314_transform
theorem leaf01314_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01314=true := by decide +kernel
#print axioms leaf01314_sign
theorem leaf01314_log : RationalLog.accepts (4400767117/4294967296) (52258863/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01314_log
def leaf01314 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (83881081/100000000000) (4400767117/4294967296) (52258863/4294967296) 0 8 ![60,0,4] ![(15/128),0,(15/16)] ![(1/128),1,(1/16)] affine01314
theorem leaf01314_checked : FastNestedCellData.accepts 1 2 4 leaf01314=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (83881081/100000000000) (4400767117/4294967296) (52258863/4294967296) 0 8 ![60,0,4] ![(15/128),0,(15/16)] ![(1/128),1,(1/16)] 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000 raw01314 affine01314
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01314_raw leaf01314_rectangular
    leaf01314_transform leaf01314_sign leaf01314_log
#print axioms leaf01314_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
