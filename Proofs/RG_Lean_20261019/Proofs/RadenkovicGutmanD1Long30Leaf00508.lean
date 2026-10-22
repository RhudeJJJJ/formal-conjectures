/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00508 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 24050677973852361183804470067200000000000 19066061443971538121535945194710759374848 182794616191763884614109626368000000000000))
theorem leaf00508_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 24050677973852361183804470067200000000000 19066061443971538121535945194710759374848 182794616191763884614109626368000000000000 raw00508=true := by decide +kernel
#print axioms leaf00508_raw
theorem leaf00508_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00508=true := by decide +kernel
#print axioms leaf00508_rectangular
def affine00508 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00508 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00508_transform : affine00508=(NestedInteger.clearedAll 3 raw00508 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00508_transform
theorem leaf00508_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00508=true := by decide +kernel
#print axioms leaf00508_sign
theorem leaf00508_log : RationalLog.accepts (3083224865/4294967296) (-44488865/268435456) 1 8=true := by decide +kernel
#print axioms leaf00508_log
def leaf00508 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (26075797309/250000000000) (3083224865/4294967296) (-44488865/268435456) 1 8 ![60,0,4] ![(11/800),0,(1/4)] ![(1/3200),1,(1/4)] affine00508
theorem leaf00508_checked : FastNestedCellData.accepts 1 2 4 leaf00508=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (26075797309/250000000000) (3083224865/4294967296) (-44488865/268435456) 1 8 ![60,0,4] ![(11/800),0,(1/4)] ![(1/3200),1,(1/4)] 24050677973852361183804470067200000000000 19066061443971538121535945194710759374848 182794616191763884614109626368000000000000 raw00508 affine00508
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00508_raw leaf00508_rectangular
    leaf00508_transform leaf00508_sign leaf00508_log
#print axioms leaf00508_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
