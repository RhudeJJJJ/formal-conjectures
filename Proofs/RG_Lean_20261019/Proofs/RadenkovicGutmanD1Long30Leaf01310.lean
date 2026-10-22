/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01310 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000))
theorem leaf01310_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000 raw01310=true := by decide +kernel
#print axioms leaf01310_raw
theorem leaf01310_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01310=true := by decide +kernel
#print axioms leaf01310_rectangular
def affine01310 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01310 (IntegerComputedClassCell.leftNumerator ![(15/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/128),0,0] ![(1/128),1,(1/2)]))
theorem leaf01310_transform : affine01310=(NestedInteger.clearedAll 3 raw01310 (IntegerComputedClassCell.leftNumerator ![(15/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/128),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01310_transform
theorem leaf01310_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01310=true := by decide +kernel
#print axioms leaf01310_sign
theorem leaf01310_log : RationalLog.accepts (4400767117/4294967296) (52258863/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01310_log
def leaf01310 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (83881081/100000000000) (4400767117/4294967296) (52258863/4294967296) 0 8 ![60,0,4] ![(15/128),0,0] ![(1/128),1,(1/2)] affine01310
theorem leaf01310_checked : FastNestedCellData.accepts 1 2 4 leaf01310=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (83881081/100000000000) (4400767117/4294967296) (52258863/4294967296) 0 8 ![60,0,4] ![(15/128),0,0] ![(1/128),1,(1/2)] 154733283383310086957537689600000000000 158677885673872143074060003492130455552 189170053344772873246662144819200000000000 raw01310 affine01310
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01310_raw leaf01310_rectangular
    leaf01310_transform leaf01310_sign leaf01310_log
#print axioms leaf01310_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
