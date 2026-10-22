/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00494 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 35144427040436905563786733158400000000000 31511014463104560550564999481881259933696 661584971790877449879941650841600000000000))
theorem leaf00494_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 35144427040436905563786733158400000000000 31511014463104560550564999481881259933696 661584971790877449879941650841600000000000 raw00494=true := by decide +kernel
#print axioms leaf00494_raw
theorem leaf00494_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00494=true := by decide +kernel
#print axioms leaf00494_rectangular
def affine00494 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00494 (IntegerComputedClassCell.leftNumerator ![(41/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00494_transform : affine00494=(NestedInteger.clearedAll 3 raw00494 (IntegerComputedClassCell.leftNumerator ![(41/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00494_transform
theorem leaf00494_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00494=true := by decide +kernel
#print axioms leaf00494_sign
theorem leaf00494_log : RationalLog.accepts (3675852079/4294967296) (-334275143/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00494_log
def leaf00494 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9525916037/200000000000) (3675852079/4294967296) (-334275143/4294967296) 1 8 ![60,0,4] ![(41/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00494
theorem leaf00494_checked : FastNestedCellData.accepts 1 2 4 leaf00494=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9525916037/200000000000) (3675852079/4294967296) (-334275143/4294967296) 1 8 ![60,0,4] ![(41/3200),0,(1/2)] ![(1/3200),1,(1/2)] 35144427040436905563786733158400000000000 31511014463104560550564999481881259933696 661584971790877449879941650841600000000000 raw00494 affine00494
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00494_raw leaf00494_rectangular
    leaf00494_transform leaf00494_sign leaf00494_log
#print axioms leaf00494_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
