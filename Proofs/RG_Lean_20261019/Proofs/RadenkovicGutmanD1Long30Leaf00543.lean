/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00543 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 553771604348106241076201783296000000000000 425297949541749394929117856723793575149568 3541786166295743329663065260032000000000000))
theorem leaf00543_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 553771604348106241076201783296000000000000 425297949541749394929117856723793575149568 3541786166295743329663065260032000000000000 raw00543=true := by decide +kernel
#print axioms leaf00543_raw
theorem leaf00543_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00543=true := by decide +kernel
#print axioms leaf00543_rectangular
def affine00543 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00543 (IntegerComputedClassCell.leftNumerator ![(51/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(51/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(51/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00543_transform : affine00543=(NestedInteger.clearedAll 3 raw00543 (IntegerComputedClassCell.leftNumerator ![(51/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(51/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(51/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00543_transform
theorem leaf00543_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00543=true := by decide +kernel
#print axioms leaf00543_sign
theorem leaf00543_log : RationalLog.accepts (1472459641/2147483648) (-6331093/33554432) 1 8=true := by decide +kernel
#print axioms leaf00543_log
def leaf00543 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (120080075299/1000000000000) (1472459641/2147483648) (-6331093/33554432) 1 8 ![60,0,4] ![(51/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00543
theorem leaf00543_checked : FastNestedCellData.accepts 1 2 4 leaf00543=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (120080075299/1000000000000) (1472459641/2147483648) (-6331093/33554432) 1 8 ![60,0,4] ![(51/3200),0,(1/4)] ![(1/3200),1,(1/4)] 553771604348106241076201783296000000000000 425297949541749394929117856723793575149568 3541786166295743329663065260032000000000000 raw00543 affine00543
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00543_raw leaf00543_rectangular
    leaf00543_transform leaf00543_sign leaf00543_log
#print axioms leaf00543_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
