/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00971 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 100647383331690327144277800386560000000000 42943724240486012581825964831101239164928 62966119091286932964032013926400000000000))
theorem leaf00971_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 100647383331690327144277800386560000000000 42943724240486012581825964831101239164928 62966119091286932964032013926400000000000 raw00971=true := by decide +kernel
#print axioms leaf00971_raw
theorem leaf00971_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00971=true := by decide +kernel
#print axioms leaf00971_rectangular
def affine00971 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00971 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/16)] ![(1/160),1,(1/16)]))
theorem leaf00971_transform : affine00971=(NestedInteger.clearedAll 3 raw00971 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/16)] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00971_transform
theorem leaf00971_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00971=true := by decide +kernel
#print axioms leaf00971_sign
theorem leaf00971_log : RationalLog.accepts (1089501115/4294967296) (-2945755021/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00971_log
def leaf00971 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (136402639579/200000000000) (1089501115/4294967296) (-2945755021/4294967296) 2 8 ![60,0,4] ![(9/80),0,(1/16)] ![(1/160),1,(1/16)] affine00971
theorem leaf00971_checked : FastNestedCellData.accepts 1 2 4 leaf00971=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (136402639579/200000000000) (1089501115/4294967296) (-2945755021/4294967296) 2 8 ![60,0,4] ![(9/80),0,(1/16)] ![(1/160),1,(1/16)] 100647383331690327144277800386560000000000 42943724240486012581825964831101239164928 62966119091286932964032013926400000000000 raw00971 affine00971
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00971_raw leaf00971_rectangular
    leaf00971_transform leaf00971_sign leaf00971_log
#print axioms leaf00971_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
