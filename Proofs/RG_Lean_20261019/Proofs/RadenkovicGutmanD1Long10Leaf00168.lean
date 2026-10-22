/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00168 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 174353703890292984651611897856000000000000 1803547461556775393753627205196459278336 3975345531549030299941732352000000000000))
theorem leaf00168_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 174353703890292984651611897856000000000000 1803547461556775393753627205196459278336 3975345531549030299941732352000000000000 raw00168=true := by decide +kernel
#print axioms leaf00168_raw
theorem leaf00168_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00168=true := by decide +kernel
#print axioms leaf00168_rectangular
def affine00168 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00168 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(73/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00168_transform : affine00168=(NestedInteger.clearedAll 3 raw00168 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(73/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00168_transform
theorem leaf00168_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00168=true := by decide +kernel
#print axioms leaf00168_sign
theorem leaf00168_log : RationalLog.accepts (7640583/1073741824) (-10620232379/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00168_log
def leaf00168 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (453683194893/1000000000000) (7640583/1073741824) (-10620232379/4294967296) 8 8 ![52,0,4] ![(73/3200),0,0] ![(3/3200),1,(1/4)] affine00168
theorem leaf00168_checked : FastNestedCellData.accepts 1 0 4 leaf00168=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (453683194893/1000000000000) (7640583/1073741824) (-10620232379/4294967296) 8 8 ![52,0,4] ![(73/3200),0,0] ![(3/3200),1,(1/4)] 174353703890292984651611897856000000000000 1803547461556775393753627205196459278336 3975345531549030299941732352000000000000 raw00168 affine00168
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00168_raw leaf00168_rectangular
    leaf00168_transform leaf00168_sign leaf00168_log
#print axioms leaf00168_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
