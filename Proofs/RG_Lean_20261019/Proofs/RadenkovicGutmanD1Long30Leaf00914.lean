/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00914 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1071560658351782520743985676288000000000000 717865792879547073818919192394425216008192 3089485988802578067523094183936000000000000))
theorem leaf00914_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1071560658351782520743985676288000000000000 717865792879547073818919192394425216008192 3089485988802578067523094183936000000000000 raw00914=true := by decide +kernel
#print axioms leaf00914_raw
theorem leaf00914_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00914=true := by decide +kernel
#print axioms leaf00914_rectangular
def affine00914 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00914 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00914_transform : affine00914=(NestedInteger.clearedAll 3 raw00914 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00914_transform
theorem leaf00914_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00914=true := by decide +kernel
#print axioms leaf00914_sign
theorem leaf00914_log : RationalLog.accepts (1167399731/2147483648) (-1308929839/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00914_log
def leaf00914 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (232357678747/1000000000000) (1167399731/2147483648) (-1308929839/4294967296) 1 8 ![60,0,4] ![(23/320),0,(1/2)] ![(1/320),1,(1/2)] affine00914
theorem leaf00914_checked : FastNestedCellData.accepts 1 2 4 leaf00914=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (232357678747/1000000000000) (1167399731/2147483648) (-1308929839/4294967296) 1 8 ![60,0,4] ![(23/320),0,(1/2)] ![(1/320),1,(1/2)] 1071560658351782520743985676288000000000000 717865792879547073818919192394425216008192 3089485988802578067523094183936000000000000 raw00914 affine00914
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00914_raw leaf00914_rectangular
    leaf00914_transform leaf00914_sign leaf00914_log
#print axioms leaf00914_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
