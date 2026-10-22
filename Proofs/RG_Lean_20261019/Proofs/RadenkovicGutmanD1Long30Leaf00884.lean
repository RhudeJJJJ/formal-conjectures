/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00884 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 59873571745211478360547393536000000000000 41112169070255084294877964752206532968448 197913296470075786557330030592000000000000))
theorem leaf00884_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 59873571745211478360547393536000000000000 41112169070255084294877964752206532968448 197913296470075786557330030592000000000000 raw00884=true := by decide +kernel
#print axioms leaf00884_raw
theorem leaf00884_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00884=true := by decide +kernel
#print axioms leaf00884_rectangular
def affine00884 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00884 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00884_transform : affine00884=(NestedInteger.clearedAll 3 raw00884 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00884_transform
theorem leaf00884_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00884=true := by decide +kernel
#print axioms leaf00884_sign
theorem leaf00884_log : RationalLog.accepts (610472203/1073741824) (-303156033/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00884_log
def leaf00884 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (103864090497/500000000000) (610472203/1073741824) (-303156033/1073741824) 1 8 ![60,0,4] ![(1/16),0,(1/2)] ![(1/640),1,(1/2)] affine00884
theorem leaf00884_checked : FastNestedCellData.accepts 1 2 4 leaf00884=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (103864090497/500000000000) (610472203/1073741824) (-303156033/1073741824) 1 8 ![60,0,4] ![(1/16),0,(1/2)] ![(1/640),1,(1/2)] 59873571745211478360547393536000000000000 41112169070255084294877964752206532968448 197913296470075786557330030592000000000000 raw00884 affine00884
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00884_raw leaf00884_rectangular
    leaf00884_transform leaf00884_sign leaf00884_log
#print axioms leaf00884_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
