/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00913 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 613568832674418965439771049984000000000000 322310533466585544984787390177181932978176 807513301211231448708627300352000000000000))
theorem leaf00913_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 613568832674418965439771049984000000000000 322310533466585544984787390177181932978176 807513301211231448708627300352000000000000 raw00913=true := by decide +kernel
#print axioms leaf00913_raw
theorem leaf00913_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00913=true := by decide +kernel
#print axioms leaf00913_rectangular
def affine00913 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00913 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00913_transform : affine00913=(NestedInteger.clearedAll 3 raw00913 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00913_transform
theorem leaf00913_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00913=true := by decide +kernel
#print axioms leaf00913_sign
theorem leaf00913_log : RationalLog.accepts (806269119/2147483648) (-2103749051/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00913_log
def leaf00913 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (399139596813/1000000000000) (806269119/2147483648) (-2103749051/4294967296) 2 8 ![60,0,4] ![(23/320),0,(1/4)] ![(1/320),1,(1/4)] affine00913
theorem leaf00913_checked : FastNestedCellData.accepts 1 2 4 leaf00913=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (399139596813/1000000000000) (806269119/2147483648) (-2103749051/4294967296) 2 8 ![60,0,4] ![(23/320),0,(1/4)] ![(1/320),1,(1/4)] 613568832674418965439771049984000000000000 322310533466585544984787390177181932978176 807513301211231448708627300352000000000000 raw00913 affine00913
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00913_raw leaf00913_rectangular
    leaf00913_transform leaf00913_sign leaf00913_log
#print axioms leaf00913_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
