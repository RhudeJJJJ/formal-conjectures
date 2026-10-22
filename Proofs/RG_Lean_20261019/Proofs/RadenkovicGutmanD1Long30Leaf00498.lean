/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00498 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 115005368681980821165737771008000000000000 92020338787513202472813950384808765947904 922498042180131537935860236288000000000000))
theorem leaf00498_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 115005368681980821165737771008000000000000 92020338787513202472813950384808765947904 922498042180131537935860236288000000000000 raw00498=true := by decide +kernel
#print axioms leaf00498_raw
theorem leaf00498_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00498=true := by decide +kernel
#print axioms leaf00498_rectangular
def affine00498 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00498 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00498_transform : affine00498=(NestedInteger.clearedAll 3 raw00498 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00498_transform
theorem leaf00498_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00498=true := by decide +kernel
#print axioms leaf00498_sign
theorem leaf00498_log : RationalLog.accepts (1562431953/2147483648) (-683014101/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00498_log
def leaf00498 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (49875628229/500000000000) (1562431953/2147483648) (-683014101/4294967296) 1 8 ![60,0,4] ![(21/1600),0,(1/4)] ![(1/3200),1,(1/4)] affine00498
theorem leaf00498_checked : FastNestedCellData.accepts 1 2 4 leaf00498=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (49875628229/500000000000) (1562431953/2147483648) (-683014101/4294967296) 1 8 ![60,0,4] ![(21/1600),0,(1/4)] ![(1/3200),1,(1/4)] 115005368681980821165737771008000000000000 92020338787513202472813950384808765947904 922498042180131537935860236288000000000000 raw00498 affine00498
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00498_raw leaf00498_rectangular
    leaf00498_transform leaf00498_sign leaf00498_log
#print axioms leaf00498_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
