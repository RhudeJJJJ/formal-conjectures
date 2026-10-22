/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00993 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 534889083913225160056167727104000000000000 326560851280961431704845445356148869824512 703882429699421816324492361728000000000000))
theorem leaf00993_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 534889083913225160056167727104000000000000 326560851280961431704845445356148869824512 703882429699421816324492361728000000000000 raw00993=true := by decide +kernel
#print axioms leaf00993_raw
theorem leaf00993_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00993=true := by decide +kernel
#print axioms leaf00993_rectangular
def affine00993 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00993 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00993_transform : affine00993=(NestedInteger.clearedAll 3 raw00993 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00993_transform
theorem leaf00993_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00993=true := by decide +kernel
#print axioms leaf00993_sign
theorem leaf00993_log : RationalLog.accepts (895583911/2147483648) (-939068993/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00993_log
def leaf00993 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (231971162727/500000000000) (895583911/2147483648) (-939068993/2147483648) 2 8 ![60,0,4] ![(11/80),0,(1/4)] ![(1/160),1,(1/4)] affine00993
theorem leaf00993_checked : FastNestedCellData.accepts 1 2 4 leaf00993=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (231971162727/500000000000) (895583911/2147483648) (-939068993/2147483648) 2 8 ![60,0,4] ![(11/80),0,(1/4)] ![(1/160),1,(1/4)] 534889083913225160056167727104000000000000 326560851280961431704845445356148869824512 703882429699421816324492361728000000000000 raw00993 affine00993
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00993_raw leaf00993_rectangular
    leaf00993_transform leaf00993_sign leaf00993_log
#print axioms leaf00993_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
