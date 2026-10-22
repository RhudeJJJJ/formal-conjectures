/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00006 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 140908036483428593887756471500800000000000 746441121689092500153339145038594048 19543822597387084357435392000000000000))
theorem leaf00006_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 140908036483428593887756471500800000000000 746441121689092500153339145038594048 19543822597387084357435392000000000000 raw00006=true := by decide +kernel
#print axioms leaf00006_raw
theorem leaf00006_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00006=true := by decide +kernel
#print axioms leaf00006_rectangular
def affine00006 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00006 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/2000),0,0] ![(1/4000),1,(1/4)]))
theorem leaf00006_transform : affine00006=(NestedInteger.clearedAll 3 raw00006 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/2000),0,0] ![(1/4000),1,(1/4)])) := by decide +kernel
#print axioms leaf00006_transform
theorem leaf00006_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00006=true := by decide +kernel
#print axioms leaf00006_sign
theorem leaf00006_log : RationalLog.accepts (21915/4294967296) (-817774085/134217728) 18 8=true := by decide +kernel
#print axioms leaf00006_log
def leaf00006 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (38193199819/1000000000000) (21915/4294967296) (-817774085/134217728) 18 8 ![52,0,4] ![(3/2000),0,0] ![(1/4000),1,(1/4)] affine00006
theorem leaf00006_checked : FastNestedCellData.accepts 1 0 4 leaf00006=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (38193199819/1000000000000) (21915/4294967296) (-817774085/134217728) 18 8 ![52,0,4] ![(3/2000),0,0] ![(1/4000),1,(1/4)] 140908036483428593887756471500800000000000 746441121689092500153339145038594048 19543822597387084357435392000000000000 raw00006 affine00006
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00006_raw leaf00006_rectangular
    leaf00006_transform leaf00006_sign leaf00006_log
#print axioms leaf00006_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
