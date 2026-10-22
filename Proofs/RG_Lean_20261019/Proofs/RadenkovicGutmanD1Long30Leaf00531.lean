/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00531 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 484688298170723164836629315584000000000000 194926824896609425183150234862712776556544 463669804070398994494485692416000000000000))
theorem leaf00531_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 484688298170723164836629315584000000000000 194926824896609425183150234862712776556544 463669804070398994494485692416000000000000 raw00531=true := by decide +kernel
#print axioms leaf00531_raw
theorem leaf00531_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00531=true := by decide +kernel
#print axioms leaf00531_rectangular
def affine00531 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00531 (IntegerComputedClassCell.leftNumerator ![(49/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(49/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(49/3200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00531_transform : affine00531=(NestedInteger.clearedAll 3 raw00531 (IntegerComputedClassCell.leftNumerator ![(49/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(49/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(49/3200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00531_transform
theorem leaf00531_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00531=true := by decide +kernel
#print axioms leaf00531_sign
theorem leaf00531_log : RationalLog.accepts (1216069079/4294967296) (-2709738641/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00531_log
def leaf00531 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (105100021171/250000000000) (1216069079/4294967296) (-2709738641/4294967296) 2 8 ![60,0,4] ![(49/3200),0,(1/16)] ![(1/3200),1,(1/16)] affine00531
theorem leaf00531_checked : FastNestedCellData.accepts 1 2 4 leaf00531=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (105100021171/250000000000) (1216069079/4294967296) (-2709738641/4294967296) 2 8 ![60,0,4] ![(49/3200),0,(1/16)] ![(1/3200),1,(1/16)] 484688298170723164836629315584000000000000 194926824896609425183150234862712776556544 463669804070398994494485692416000000000000 raw00531 affine00531
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00531_raw leaf00531_rectangular
    leaf00531_transform leaf00531_sign leaf00531_log
#print axioms leaf00531_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
