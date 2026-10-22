/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01087 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 253135136721624063227359710412800000000000 277283972283402608129169624061577961406464 1010327238387003629816516706304000000000000))
theorem leaf01087_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 253135136721624063227359710412800000000000 277283972283402608129169624061577961406464 1010327238387003629816516706304000000000000 raw01087=true := by decide +kernel
#print axioms leaf01087_raw
theorem leaf01087_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01087=true := by decide +kernel
#print axioms leaf01087_rectangular
def affine01087 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01087 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/8)] ![(3/80),1,(1/8)]))
theorem leaf01087_transform : affine01087=(NestedInteger.clearedAll 3 raw01087 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/8)] ![(3/80),1,(1/8)])) := by decide +kernel
#print axioms leaf01087_transform
theorem leaf01087_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01087=true := by decide +kernel
#print axioms leaf01087_sign
theorem leaf01087_log : RationalLog.accepts (3691556405/4294967296) (-162560001/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01087_log
def leaf01087 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (137224832583/500000000000) (3691556405/4294967296) (-162560001/2147483648) 1 8 ![60,0,4] ![(17/40),0,(1/8)] ![(3/80),1,(1/8)] affine01087
theorem leaf01087_checked : FastNestedCellData.accepts 1 2 4 leaf01087=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (137224832583/500000000000) (3691556405/4294967296) (-162560001/2147483648) 1 8 ![60,0,4] ![(17/40),0,(1/8)] ![(3/80),1,(1/8)] 253135136721624063227359710412800000000000 277283972283402608129169624061577961406464 1010327238387003629816516706304000000000000 raw01087 affine01087
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01087_raw leaf01087_rectangular
    leaf01087_transform leaf01087_sign leaf01087_log
#print axioms leaf01087_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
