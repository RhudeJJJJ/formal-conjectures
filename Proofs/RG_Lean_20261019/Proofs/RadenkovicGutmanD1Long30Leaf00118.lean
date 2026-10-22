/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00118 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5932612839175985492612087808000000000000 5650497908403487223071924644442301005824 274524089424620098162819858432000000000000))
theorem leaf00118_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5932612839175985492612087808000000000000 5650497908403487223071924644442301005824 274524089424620098162819858432000000000000 raw00118=true := by decide +kernel
#print axioms leaf00118_raw
theorem leaf00118_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00118=true := by decide +kernel
#print axioms leaf00118_rectangular
def affine00118 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00118 (IntegerComputedClassCell.leftNumerator ![(17/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/6400),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00118_transform : affine00118=(NestedInteger.clearedAll 3 raw00118 (IntegerComputedClassCell.leftNumerator ![(17/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/6400),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00118_transform
theorem leaf00118_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00118=true := by decide +kernel
#print axioms leaf00118_sign
theorem leaf00118_log : RationalLog.accepts (2004113417/2147483648) (-148380383/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00118_log
def leaf00118 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (5145721383/250000000000) (2004113417/2147483648) (-148380383/4294967296) 1 8 ![60,0,4] ![(17/6400),0,(1/4)] ![(3/32000),1,(1/4)] affine00118
theorem leaf00118_checked : FastNestedCellData.accepts 1 2 4 leaf00118=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (5145721383/250000000000) (2004113417/2147483648) (-148380383/4294967296) 1 8 ![60,0,4] ![(17/6400),0,(1/4)] ![(3/32000),1,(1/4)] 5932612839175985492612087808000000000000 5650497908403487223071924644442301005824 274524089424620098162819858432000000000000 raw00118 affine00118
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00118_raw leaf00118_rectangular
    leaf00118_transform leaf00118_sign leaf00118_log
#print axioms leaf00118_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
