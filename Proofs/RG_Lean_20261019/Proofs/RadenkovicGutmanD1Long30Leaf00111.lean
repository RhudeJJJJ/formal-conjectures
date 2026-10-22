/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00111 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 377651362652544648216433393664000000000000 312636290890187193350505671063441762156544 3817755088779524567611509571584000000000000))
theorem leaf00111_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 377651362652544648216433393664000000000000 312636290890187193350505671063441762156544 3817755088779524567611509571584000000000000 raw00111=true := by decide +kernel
#print axioms leaf00111_raw
theorem leaf00111_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00111=true := by decide +kernel
#print axioms leaf00111_rectangular
def affine00111 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00111 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00111_transform : affine00111=(NestedInteger.clearedAll 3 raw00111 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00111_transform
theorem leaf00111_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00111=true := by decide +kernel
#print axioms leaf00111_sign
theorem leaf00111_log : RationalLog.accepts (3286435051/4294967296) (-143688427/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00111_log
def leaf00111 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (40945042783/500000000000) (3286435051/4294967296) (-143688427/1073741824) 1 8 ![60,0,4] ![(41/16000),0,(1/16)] ![(3/32000),1,(1/16)] affine00111
theorem leaf00111_checked : FastNestedCellData.accepts 1 2 4 leaf00111=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (40945042783/500000000000) (3286435051/4294967296) (-143688427/1073741824) 1 8 ![60,0,4] ![(41/16000),0,(1/16)] ![(3/32000),1,(1/16)] 377651362652544648216433393664000000000000 312636290890187193350505671063441762156544 3817755088779524567611509571584000000000000 raw00111 affine00111
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00111_raw leaf00111_rectangular
    leaf00111_transform leaf00111_sign leaf00111_log
#print axioms leaf00111_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
