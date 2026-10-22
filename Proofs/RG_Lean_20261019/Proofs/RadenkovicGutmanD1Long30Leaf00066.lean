/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00066 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1044896337789132555736317952000000000000 913574836468824129757221320167788642304 15750367359125984795340832768000000000000))
theorem leaf00066_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1044896337789132555736317952000000000000 913574836468824129757221320167788642304 15750367359125984795340832768000000000000 raw00066=true := by decide +kernel
#print axioms leaf00066_raw
theorem leaf00066_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00066=true := by decide +kernel
#print axioms leaf00066_rectangular
def affine00066 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00066 (IntegerComputedClassCell.leftNumerator ![(29/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/16000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00066_transform : affine00066=(NestedInteger.clearedAll 3 raw00066 (IntegerComputedClassCell.leftNumerator ![(29/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/16000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00066_transform
theorem leaf00066_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00066=true := by decide +kernel
#print axioms leaf00066_sign
theorem leaf00066_log : RationalLog.accepts (443663533/536870912) (-409506295/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00066_log
def leaf00066 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (14500849657/250000000000) (443663533/536870912) (-409506295/4294967296) 1 8 ![60,0,4] ![(29/16000),0,(1/16)] ![(1/16000),1,(1/16)] affine00066
theorem leaf00066_checked : FastNestedCellData.accepts 1 2 4 leaf00066=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (14500849657/250000000000) (443663533/536870912) (-409506295/4294967296) 1 8 ![60,0,4] ![(29/16000),0,(1/16)] ![(1/16000),1,(1/16)] 1044896337789132555736317952000000000000 913574836468824129757221320167788642304 15750367359125984795340832768000000000000 raw00066 affine00066
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00066_raw leaf00066_rectangular
    leaf00066_transform leaf00066_sign leaf00066_log
#print axioms leaf00066_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
