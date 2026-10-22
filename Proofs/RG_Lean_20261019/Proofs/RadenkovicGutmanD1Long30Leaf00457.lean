/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00457 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 205232588205752707552481640448000000000000 139100289764435981727586566302256727064576 781414475978268050764555354112000000000000))
theorem leaf00457_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 205232588205752707552481640448000000000000 139100289764435981727586566302256727064576 781414475978268050764555354112000000000000 raw00457=true := by decide +kernel
#print axioms leaf00457_raw
theorem leaf00457_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00457=true := by decide +kernel
#print axioms leaf00457_rectangular
def affine00457 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00457 (IntegerComputedClassCell.leftNumerator ![(3/256),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/256),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00457_transform : affine00457=(NestedInteger.clearedAll 3 raw00457 (IntegerComputedClassCell.leftNumerator ![(3/256),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/256),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00457_transform
theorem leaf00457_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00457=true := by decide +kernel
#print axioms leaf00457_sign
theorem leaf00457_log : RationalLog.accepts (1235555537/2147483648) (-593538797/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00457_log
def leaf00457 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (89005447199/500000000000) (1235555537/2147483648) (-593538797/2147483648) 1 8 ![60,0,4] ![(3/256),0,(1/8)] ![(1/6400),1,(1/8)] affine00457
theorem leaf00457_checked : FastNestedCellData.accepts 1 2 4 leaf00457=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (89005447199/500000000000) (1235555537/2147483648) (-593538797/2147483648) 1 8 ![60,0,4] ![(3/256),0,(1/8)] ![(1/6400),1,(1/8)] 205232588205752707552481640448000000000000 139100289764435981727586566302256727064576 781414475978268050764555354112000000000000 raw00457 affine00457
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00457_raw leaf00457_rectangular
    leaf00457_transform leaf00457_sign leaf00457_log
#print axioms leaf00457_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
