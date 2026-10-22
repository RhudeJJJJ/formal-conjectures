/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00019 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 207516047476844603501025689600000000000 205240074909465711608218777395960741888 45611064560517277198541075251200000000000))
theorem leaf00019_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 207516047476844603501025689600000000000 205240074909465711608218777395960741888 45611064560517277198541075251200000000000 raw00019=true := by decide +kernel
#print axioms leaf00019_raw
theorem leaf00019_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00019=true := by decide +kernel
#print axioms leaf00019_rectangular
def affine00019 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00019 (IntegerComputedClassCell.leftNumerator ![(19/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/16000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00019_transform : affine00019=(NestedInteger.clearedAll 3 raw00019 (IntegerComputedClassCell.leftNumerator ![(19/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/16000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00019_transform
theorem leaf00019_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00019=true := by decide +kernel
#print axioms leaf00019_sign
theorem leaf00019_log : RationalLog.accepts (2114416281/2147483648) (-33324637/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00019_log
def leaf00019 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (449978699/100000000000) (2114416281/2147483648) (-33324637/4294967296) 1 8 ![60,0,4] ![(19/16000),0,(1/2)] ![(1/16000),1,(1/2)] affine00019
theorem leaf00019_checked : FastNestedCellData.accepts 1 2 4 leaf00019=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (449978699/100000000000) (2114416281/2147483648) (-33324637/4294967296) 1 8 ![60,0,4] ![(19/16000),0,(1/2)] ![(1/16000),1,(1/2)] 207516047476844603501025689600000000000 205240074909465711608218777395960741888 45611064560517277198541075251200000000000 raw00019 affine00019
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00019_raw leaf00019_rectangular
    leaf00019_transform leaf00019_sign leaf00019_log
#print axioms leaf00019_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
