/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00381 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 966534542253705422492422635520000000000 1116776975550113416988858621392978968576 3330341893315258255222505472000000000000))
theorem leaf00381_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 966534542253705422492422635520000000000 1116776975550113416988858621392978968576 3330341893315258255222505472000000000000 raw00381=true := by decide +kernel
#print axioms leaf00381_raw
theorem leaf00381_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00381=true := by decide +kernel
#print axioms leaf00381_rectangular
def affine00381 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00381 (IntegerComputedClassCell.leftNumerator ![(17/40),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/40),0,0] ![(3/80),1,(1/4)]))
theorem leaf00381_transform : affine00381=(NestedInteger.clearedAll 3 raw00381 (IntegerComputedClassCell.leftNumerator ![(17/40),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/40),0,0] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00381_transform
theorem leaf00381_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00381=true := by decide +kernel
#print axioms leaf00381_sign
theorem leaf00381_log : RationalLog.accepts (464546325/536870912) (-38841647/536870912) 1 8=true := by decide +kernel
#print axioms leaf00381_log
def leaf00381 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (167667016079/500000000000) (464546325/536870912) (-38841647/536870912) 1 8 ![52,0,4] ![(17/40),0,0] ![(3/80),1,(1/4)] affine00381
theorem leaf00381_checked : FastNestedCellData.accepts 1 0 4 leaf00381=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (167667016079/500000000000) (464546325/536870912) (-38841647/536870912) 1 8 ![52,0,4] ![(17/40),0,0] ![(3/80),1,(1/4)] 966534542253705422492422635520000000000 1116776975550113416988858621392978968576 3330341893315258255222505472000000000000 raw00381 affine00381
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00381_raw leaf00381_rectangular
    leaf00381_transform leaf00381_sign leaf00381_log
#print axioms leaf00381_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
