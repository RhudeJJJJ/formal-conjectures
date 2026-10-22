/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00203 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12562439771980903012571807744000000000000 11643950183427714949932663217249390166016 356208953268950526132840562688000000000000))
theorem leaf00203_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12562439771980903012571807744000000000000 11643950183427714949932663217249390166016 356208953268950526132840562688000000000000 raw00203=true := by decide +kernel
#print axioms leaf00203_raw
theorem leaf00203_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00203=true := by decide +kernel
#print axioms leaf00203_rectangular
def affine00203 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00203 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00203_transform : affine00203=(NestedInteger.clearedAll 3 raw00203 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00203_transform
theorem leaf00203_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00203=true := by decide +kernel
#print axioms leaf00203_sign
theorem leaf00203_log : RationalLog.accepts (1927466571/2147483648) (-232122139/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00203_log
def leaf00203 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16344269391/500000000000) (1927466571/2147483648) (-232122139/4294967296) 1 8 ![60,0,4] ![(17/4000),0,(1/4)] ![(3/32000),1,(1/4)] affine00203
theorem leaf00203_checked : FastNestedCellData.accepts 1 2 4 leaf00203=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16344269391/500000000000) (1927466571/2147483648) (-232122139/4294967296) 1 8 ![60,0,4] ![(17/4000),0,(1/4)] ![(3/32000),1,(1/4)] 12562439771980903012571807744000000000000 11643950183427714949932663217249390166016 356208953268950526132840562688000000000000 raw00203 affine00203
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00203_raw leaf00203_rectangular
    leaf00203_transform leaf00203_sign leaf00203_log
#print axioms leaf00203_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
