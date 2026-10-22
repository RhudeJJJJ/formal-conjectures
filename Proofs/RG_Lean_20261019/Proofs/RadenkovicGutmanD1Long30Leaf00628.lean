/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00628 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4269673770702476006992012902400000000000 3019733535296750864690534390357035057152 18637841366124020106833323622400000000000))
theorem leaf00628_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4269673770702476006992012902400000000000 3019733535296750864690534390357035057152 18637841366124020106833323622400000000000 raw00628=true := by decide +kernel
#print axioms leaf00628_raw
theorem leaf00628_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00628=true := by decide +kernel
#print axioms leaf00628_rectangular
def affine00628 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00628 (IntegerComputedClassCell.leftNumerator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00628_transform : affine00628=(NestedInteger.clearedAll 3 raw00628 (IntegerComputedClassCell.leftNumerator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00628_transform
theorem leaf00628_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00628=true := by decide +kernel
#print axioms leaf00628_sign
theorem leaf00628_log : RationalLog.accepts (2614084221/4294967296) (-1066290321/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00628_log
def leaf00628 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16202163523/100000000000) (2614084221/4294967296) (-1066290321/4294967296) 1 8 ![60,0,4] ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)] affine00628
theorem leaf00628_checked : FastNestedCellData.accepts 1 2 4 leaf00628=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16202163523/100000000000) (2614084221/4294967296) (-1066290321/4294967296) 1 8 ![60,0,4] ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)] 4269673770702476006992012902400000000000 3019733535296750864690534390357035057152 18637841366124020106833323622400000000000 raw00628 affine00628
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00628_raw leaf00628_rectangular
    leaf00628_transform leaf00628_sign leaf00628_log
#print axioms leaf00628_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
