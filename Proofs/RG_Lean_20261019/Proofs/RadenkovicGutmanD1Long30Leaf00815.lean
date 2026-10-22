/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00815 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 253327472688145831120880009216000000000000 18919353184391749377786104308990142840832 21526020162832076442685145088000000000000))
theorem leaf00815_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 253327472688145831120880009216000000000000 18919353184391749377786104308990142840832 21526020162832076442685145088000000000000 raw00815=true := by decide +kernel
#print axioms leaf00815_raw
theorem leaf00815_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00815=true := by decide +kernel
#print axioms leaf00815_rectangular
def affine00815 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00815 (IntegerComputedClassCell.leftNumerator ![(29/640),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/640),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00815_transform : affine00815=(NestedInteger.clearedAll 3 raw00815 (IntegerComputedClassCell.leftNumerator ![(29/640),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/640),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00815_transform
theorem leaf00815_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00815=true := by decide +kernel
#print axioms leaf00815_sign
theorem leaf00815_log : RationalLog.accepts (85358889/2147483648) (-6926037483/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00815_log
def leaf00815 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (219726556991/250000000000) (85358889/2147483648) (-6926037483/4294967296) 5 8 ![60,0,4] ![(29/640),0,0] ![(3/3200),1,(1/16)] affine00815
theorem leaf00815_checked : FastNestedCellData.accepts 1 2 4 leaf00815=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (219726556991/250000000000) (85358889/2147483648) (-6926037483/4294967296) 5 8 ![60,0,4] ![(29/640),0,0] ![(3/3200),1,(1/16)] 253327472688145831120880009216000000000000 18919353184391749377786104308990142840832 21526020162832076442685145088000000000000 raw00815 affine00815
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00815_raw leaf00815_rectangular
    leaf00815_transform leaf00815_sign leaf00815_log
#print axioms leaf00815_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
