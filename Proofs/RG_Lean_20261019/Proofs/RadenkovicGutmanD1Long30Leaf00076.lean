/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00076 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 228425042717124006022093157171200000000000 197997615037067226670931958043043621240832 3197907977468741950058426007552000000000000))
theorem leaf00076_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 228425042717124006022093157171200000000000 197997615037067226670931958043043621240832 3197907977468741950058426007552000000000000 raw00076=true := by decide +kernel
#print axioms leaf00076_raw
theorem leaf00076_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00076=true := by decide +kernel
#print axioms leaf00076_rectangular
def affine00076 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00076 (IntegerComputedClassCell.leftNumerator ![(31/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/16000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00076_transform : affine00076=(NestedInteger.clearedAll 3 raw00076 (IntegerComputedClassCell.leftNumerator ![(31/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/16000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00076_transform
theorem leaf00076_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00076=true := by decide +kernel
#print axioms leaf00076_sign
theorem leaf00076_log : RationalLog.accepts (3505794535/4294967296) (-435996683/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00076_log
def leaf00076 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (61914731891/1000000000000) (3505794535/4294967296) (-435996683/4294967296) 1 8 ![60,0,4] ![(31/16000),0,(1/16)] ![(1/16000),1,(1/16)] affine00076
theorem leaf00076_checked : FastNestedCellData.accepts 1 2 4 leaf00076=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (61914731891/1000000000000) (3505794535/4294967296) (-435996683/4294967296) 1 8 ![60,0,4] ![(31/16000),0,(1/16)] ![(1/16000),1,(1/16)] 228425042717124006022093157171200000000000 197997615037067226670931958043043621240832 3197907977468741950058426007552000000000000 raw00076 affine00076
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00076_raw leaf00076_rectangular
    leaf00076_transform leaf00076_sign leaf00076_log
#print axioms leaf00076_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
