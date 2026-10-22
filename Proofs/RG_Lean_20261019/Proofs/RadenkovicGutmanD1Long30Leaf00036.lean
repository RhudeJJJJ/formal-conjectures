/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00036 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 213277576316691598570126573568000000000000 191396210320819209127801325503548235972608 4138546781898283906257622401024000000000000))
theorem leaf00036_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 213277576316691598570126573568000000000000 191396210320819209127801325503548235972608 4138546781898283906257622401024000000000000 raw00036=true := by decide +kernel
#print axioms leaf00036_raw
theorem leaf00036_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00036=true := by decide +kernel
#print axioms leaf00036_rectangular
def affine00036 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00036 (IntegerComputedClassCell.leftNumerator ![(23/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/16000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00036_transform : affine00036=(NestedInteger.clearedAll 3 raw00036 (IntegerComputedClassCell.leftNumerator ![(23/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/16000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00036_transform
theorem leaf00036_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00036=true := by decide +kernel
#print axioms leaf00036_sign
theorem leaf00036_log : RationalLog.accepts (1841974839/2147483648) (-329549617/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00036_log
def leaf00036 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (46247202317/1000000000000) (1841974839/2147483648) (-329549617/4294967296) 1 8 ![60,0,4] ![(23/16000),0,(1/16)] ![(1/16000),1,(1/16)] affine00036
theorem leaf00036_checked : FastNestedCellData.accepts 1 2 4 leaf00036=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (46247202317/1000000000000) (1841974839/2147483648) (-329549617/4294967296) 1 8 ![60,0,4] ![(23/16000),0,(1/16)] ![(1/16000),1,(1/16)] 213277576316691598570126573568000000000000 191396210320819209127801325503548235972608 4138546781898283906257622401024000000000000 raw00036 affine00036
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00036_raw leaf00036_rectangular
    leaf00036_transform leaf00036_sign leaf00036_log
#print axioms leaf00036_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
