/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00756 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2353726910567612429092939366400000000000 608620426748042997254127346373495881728 931623023828727076787060736000000000000))
theorem leaf00756_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2353726910567612429092939366400000000000 608620426748042997254127346373495881728 931623023828727076787060736000000000000 raw00756=true := by decide +kernel
#print axioms leaf00756_raw
theorem leaf00756_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00756=true := by decide +kernel
#print axioms leaf00756_rectangular
def affine00756 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00756 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00756_transform : affine00756=(NestedInteger.clearedAll 3 raw00756 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00756_transform
theorem leaf00756_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00756=true := by decide +kernel
#print axioms leaf00756_sign
theorem leaf00756_log : RationalLog.accepts (671739915/4294967296) (-3984286617/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00756_log
def leaf00756 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (20415326639/31250000000) (671739915/4294967296) (-3984286617/4294967296) 3 8 ![60,0,4] ![(109/3200),0,(1/16)] ![(3/3200),1,(1/16)] affine00756
theorem leaf00756_checked : FastNestedCellData.accepts 1 2 4 leaf00756=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (20415326639/31250000000) (671739915/4294967296) (-3984286617/4294967296) 3 8 ![60,0,4] ![(109/3200),0,(1/16)] ![(3/3200),1,(1/16)] 2353726910567612429092939366400000000000 608620426748042997254127346373495881728 931623023828727076787060736000000000000 raw00756 affine00756
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00756_raw leaf00756_rectangular
    leaf00756_transform leaf00756_sign leaf00756_log
#print axioms leaf00756_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
