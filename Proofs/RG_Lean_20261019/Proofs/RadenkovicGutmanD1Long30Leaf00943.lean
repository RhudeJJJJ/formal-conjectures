/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00943 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 502843394651599445684645789696000000000000 269124430049658437553004916455282632032256 617049654265206742229069070336000000000000))
theorem leaf00943_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 502843394651599445684645789696000000000000 269124430049658437553004916455282632032256 617049654265206742229069070336000000000000 raw00943=true := by decide +kernel
#print axioms leaf00943_raw
theorem leaf00943_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00943=true := by decide +kernel
#print axioms leaf00943_rectangular
def affine00943 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00943 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00943_transform : affine00943=(NestedInteger.clearedAll 3 raw00943 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00943_transform
theorem leaf00943_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00943=true := by decide +kernel
#print axioms leaf00943_sign
theorem leaf00943_log : RationalLog.accepts (400148609/1073741824) (-2119714303/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00943_log
def leaf00943 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (436147120721/1000000000000) (400148609/1073741824) (-2119714303/4294967296) 2 8 ![60,0,4] ![(29/320),0,(1/4)] ![(1/320),1,(1/4)] affine00943
theorem leaf00943_checked : FastNestedCellData.accepts 1 2 4 leaf00943=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (436147120721/1000000000000) (400148609/1073741824) (-2119714303/4294967296) 2 8 ![60,0,4] ![(29/320),0,(1/4)] ![(1/320),1,(1/4)] 502843394651599445684645789696000000000000 269124430049658437553004916455282632032256 617049654265206742229069070336000000000000 raw00943 affine00943
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00943_raw leaf00943_rectangular
    leaf00943_transform leaf00943_sign leaf00943_log
#print axioms leaf00943_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
