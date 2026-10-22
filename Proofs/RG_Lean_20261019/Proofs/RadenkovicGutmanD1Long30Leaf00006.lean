/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00006 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 529777269937797898461354393600000000000 488060775105679711008950628457044246528 14161819695548441526163367526400000000000))
theorem leaf00006_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 529777269937797898461354393600000000000 488060775105679711008950628457044246528 14161819695548441526163367526400000000000 raw00006=true := by decide +kernel
#print axioms leaf00006_raw
theorem leaf00006_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00006=true := by decide +kernel
#print axioms leaf00006_rectangular
def affine00006 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00006 (IntegerComputedClassCell.leftNumerator ![(17/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/16000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00006_transform : affine00006=(NestedInteger.clearedAll 3 raw00006 (IntegerComputedClassCell.leftNumerator ![(17/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/16000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00006_transform
theorem leaf00006_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00006=true := by decide +kernel
#print axioms leaf00006_sign
theorem leaf00006_log : RationalLog.accepts (3824947029/4294967296) (-7777873/134217728) 1 8=true := by decide +kernel
#print axioms leaf00006_log
def leaf00006 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1723157001/50000000000) (3824947029/4294967296) (-7777873/134217728) 1 8 ![60,0,4] ![(17/16000),0,(1/16)] ![(1/16000),1,(1/16)] affine00006
theorem leaf00006_checked : FastNestedCellData.accepts 1 2 4 leaf00006=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1723157001/50000000000) (3824947029/4294967296) (-7777873/134217728) 1 8 ![60,0,4] ![(17/16000),0,(1/16)] ![(1/16000),1,(1/16)] 529777269937797898461354393600000000000 488060775105679711008950628457044246528 14161819695548441526163367526400000000000 raw00006 affine00006
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00006_raw leaf00006_rectangular
    leaf00006_transform leaf00006_sign leaf00006_log
#print axioms leaf00006_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
