/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00027 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 617160799139559089097785999360000000000 587231002971308604603957753458863374336 28083442860433371842719839682560000000000))
theorem leaf00027_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 617160799139559089097785999360000000000 587231002971308604603957753458863374336 28083442860433371842719839682560000000000 raw00027=true := by decide +kernel
#print axioms leaf00027_raw
theorem leaf00027_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00027=true := by decide +kernel
#print axioms leaf00027_rectangular
def affine00027 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00027 (IntegerComputedClassCell.leftNumerator ![(21/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/16000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00027_transform : affine00027=(NestedInteger.clearedAll 3 raw00027 (IntegerComputedClassCell.leftNumerator ![(21/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/16000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00027_transform
theorem leaf00027_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00027=true := by decide +kernel
#print axioms leaf00027_sign
theorem leaf00027_log : RationalLog.accepts (4002975691/4294967296) (-151195627/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00027_log
def leaf00027 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (836408849/40000000000) (4002975691/4294967296) (-151195627/4294967296) 1 8 ![60,0,4] ![(21/16000),0,(1/8)] ![(1/16000),1,(1/8)] affine00027
theorem leaf00027_checked : FastNestedCellData.accepts 1 2 4 leaf00027=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (836408849/40000000000) (4002975691/4294967296) (-151195627/4294967296) 1 8 ![60,0,4] ![(21/16000),0,(1/8)] ![(1/16000),1,(1/8)] 617160799139559089097785999360000000000 587231002971308604603957753458863374336 28083442860433371842719839682560000000000 raw00027 affine00027
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00027_raw leaf00027_rectangular
    leaf00027_transform leaf00027_sign leaf00027_log
#print axioms leaf00027_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
