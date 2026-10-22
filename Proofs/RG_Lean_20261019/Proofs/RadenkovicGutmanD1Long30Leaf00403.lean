/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00403 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1097464645267447452186286489600000000000 924488520682532129099459764613730533376 12140057322727204117630943232000000000000))
theorem leaf00403_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1097464645267447452186286489600000000000 924488520682532129099459764613730533376 12140057322727204117630943232000000000000 raw00403=true := by decide +kernel
#print axioms leaf00403_raw
theorem leaf00403_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00403=true := by decide +kernel
#print axioms leaf00403_rectangular
def affine00403 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00403 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00403_transform : affine00403=(NestedInteger.clearedAll 3 raw00403 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00403_transform
theorem leaf00403_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00403=true := by decide +kernel
#print axioms leaf00403_sign
theorem leaf00403_log : RationalLog.accepts (1680998285/2147483648) (-262968975/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00403_log
def leaf00403 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9518988421/125000000000) (1680998285/2147483648) (-262968975/2147483648) 1 8 ![60,0,4] ![(1/100),0,(1/4)] ![(1/6400),1,(1/4)] affine00403
theorem leaf00403_checked : FastNestedCellData.accepts 1 2 4 leaf00403=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9518988421/125000000000) (1680998285/2147483648) (-262968975/2147483648) 1 8 ![60,0,4] ![(1/100),0,(1/4)] ![(1/6400),1,(1/4)] 1097464645267447452186286489600000000000 924488520682532129099459764613730533376 12140057322727204117630943232000000000000 raw00403 affine00403
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00403_raw leaf00403_rectangular
    leaf00403_transform leaf00403_sign leaf00403_log
#print axioms leaf00403_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
