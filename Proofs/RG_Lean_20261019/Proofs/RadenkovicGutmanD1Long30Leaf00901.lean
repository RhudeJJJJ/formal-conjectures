/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00901 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 13464819021855612609657460228096000000000000 3868968678253934705526593481682672882286592 5300470427497288948606285381632000000000000))
theorem leaf00901_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 13464819021855612609657460228096000000000000 3868968678253934705526593481682672882286592 5300470427497288948606285381632000000000000 raw00901=true := by decide +kernel
#print axioms leaf00901_raw
theorem leaf00901_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00901=true := by decide +kernel
#print axioms leaf00901_rectangular
def affine00901 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00901 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00901_transform : affine00901=(NestedInteger.clearedAll 3 raw00901 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00901_transform
theorem leaf00901_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00901=true := by decide +kernel
#print axioms leaf00901_sign
theorem leaf00901_log : RationalLog.accepts (713388657/4294967296) (-3855104441/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00901_log
def leaf00901 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (729929301781/1000000000000) (713388657/4294967296) (-3855104441/4294967296) 3 8 ![60,0,4] ![(11/160),0,(1/16)] ![(1/640),1,(1/16)] affine00901
theorem leaf00901_checked : FastNestedCellData.accepts 1 2 4 leaf00901=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (729929301781/1000000000000) (713388657/4294967296) (-3855104441/4294967296) 3 8 ![60,0,4] ![(11/160),0,(1/16)] ![(1/640),1,(1/16)] 13464819021855612609657460228096000000000000 3868968678253934705526593481682672882286592 5300470427497288948606285381632000000000000 raw00901 affine00901
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00901_raw leaf00901_rectangular
    leaf00901_transform leaf00901_sign leaf00901_log
#print axioms leaf00901_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
