/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01213 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 9694972785290682598964382924800000000000 11076604528317406859533087036124373712896 843023672019259620819680939212800000000000))
theorem leaf01213_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 9694972785290682598964382924800000000000 11076604528317406859533087036124373712896 843023672019259620819680939212800000000000 raw01213=true := by decide +kernel
#print axioms leaf01213_raw
theorem leaf01213_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01213=true := by decide +kernel
#print axioms leaf01213_rectangular
def affine01213 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01213 (IntegerComputedClassCell.leftNumerator ![(21/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/64),0,(7/8)] ![(1/64),1,(1/16)]))
theorem leaf01213_transform : affine01213=(NestedInteger.clearedAll 3 raw01213 (IntegerComputedClassCell.leftNumerator ![(21/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/64),0,(7/8)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01213_transform
theorem leaf01213_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01213=true := by decide +kernel
#print axioms leaf01213_sign
theorem leaf01213_log : RationalLog.accepts (4843405431/4294967296) (258071987/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01213_log
def leaf01213 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2627827639/200000000000) (4843405431/4294967296) (258071987/4294967296) 0 8 ![60,0,4] ![(21/64),0,(7/8)] ![(1/64),1,(1/16)] affine01213
theorem leaf01213_checked : FastNestedCellData.accepts 1 2 4 leaf01213=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2627827639/200000000000) (4843405431/4294967296) (258071987/4294967296) 0 8 ![60,0,4] ![(21/64),0,(7/8)] ![(1/64),1,(1/16)] 9694972785290682598964382924800000000000 11076604528317406859533087036124373712896 843023672019259620819680939212800000000000 raw01213 affine01213
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01213_raw leaf01213_rectangular
    leaf01213_transform leaf01213_sign leaf01213_log
#print axioms leaf01213_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
