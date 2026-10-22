/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00518 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 122538512553306809662701568000000000000 96253616207795738328458115092783824896 884390835693218092629884928000000000000))
theorem leaf00518_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 122538512553306809662701568000000000000 96253616207795738328458115092783824896 884390835693218092629884928000000000000 raw00518=true := by decide +kernel
#print axioms leaf00518_raw
theorem leaf00518_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00518=true := by decide +kernel
#print axioms leaf00518_rectangular
def affine00518 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00518 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00518_transform : affine00518=(NestedInteger.clearedAll 3 raw00518 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00518_transform
theorem leaf00518_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00518=true := by decide +kernel
#print axioms leaf00518_sign
theorem leaf00518_log : RationalLog.accepts (760636179/1073741824) (-740344375/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00518_log
def leaf00518 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3401126951/31250000000) (760636179/1073741824) (-740344375/4294967296) 1 8 ![60,0,4] ![(23/1600),0,(1/4)] ![(1/3200),1,(1/4)] affine00518
theorem leaf00518_checked : FastNestedCellData.accepts 1 2 4 leaf00518=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3401126951/31250000000) (760636179/1073741824) (-740344375/4294967296) 1 8 ![60,0,4] ![(23/1600),0,(1/4)] ![(1/3200),1,(1/4)] 122538512553306809662701568000000000000 96253616207795738328458115092783824896 884390835693218092629884928000000000000 raw00518 affine00518
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00518_raw leaf00518_rectangular
    leaf00518_transform leaf00518_sign leaf00518_log
#print axioms leaf00518_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
