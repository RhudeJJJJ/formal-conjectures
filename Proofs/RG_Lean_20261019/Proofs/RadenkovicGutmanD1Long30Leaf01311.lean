/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01311 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000))
theorem leaf01311_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000 raw01311=true := by decide +kernel
#print axioms leaf01311_raw
theorem leaf01311_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01311=true := by decide +kernel
#print axioms leaf01311_rectangular
def affine01311 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01311 (IntegerComputedClassCell.leftNumerator ![(15/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01311_transform : affine01311=(NestedInteger.clearedAll 3 raw01311 (IntegerComputedClassCell.leftNumerator ![(15/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01311_transform
theorem leaf01311_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01311=true := by decide +kernel
#print axioms leaf01311_sign
theorem leaf01311_log : RationalLog.accepts (4400767117/4294967296) (52258863/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01311_log
def leaf01311 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (83881081/100000000000) (4400767117/4294967296) (52258863/4294967296) 0 8 ![60,0,4] ![(15/128),0,(1/2)] ![(1/128),1,(1/4)] affine01311
theorem leaf01311_checked : FastNestedCellData.accepts 1 2 4 leaf01311=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (83881081/100000000000) (4400767117/4294967296) (52258863/4294967296) 0 8 ![60,0,4] ![(15/128),0,(1/2)] ![(1/128),1,(1/4)] 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000 raw01311 affine01311
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01311_raw leaf01311_rectangular
    leaf01311_transform leaf01311_sign leaf01311_log
#print axioms leaf01311_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
