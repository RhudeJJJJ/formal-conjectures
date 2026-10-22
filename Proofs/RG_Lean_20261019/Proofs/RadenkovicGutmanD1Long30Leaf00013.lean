/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00013 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1624891863628463377977578618880000000000 1590518250256346525959025001497616187392 180565142602940635543024697344000000000000))
theorem leaf00013_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1624891863628463377977578618880000000000 1590518250256346525959025001497616187392 180565142602940635543024697344000000000000 raw00013=true := by decide +kernel
#print axioms leaf00013_raw
theorem leaf00013_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00013=true := by decide +kernel
#print axioms leaf00013_rectangular
def affine00013 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00013 (IntegerComputedClassCell.leftNumerator ![(9/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/8000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00013_transform : affine00013=(NestedInteger.clearedAll 3 raw00013 (IntegerComputedClassCell.leftNumerator ![(9/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/8000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00013_transform
theorem leaf00013_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00013=true := by decide +kernel
#print axioms leaf00013_sign
theorem leaf00013_log : RationalLog.accepts (2083700525/2147483648) (-64749565/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00013_log
def leaf00013 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8808556443/1000000000000) (2083700525/2147483648) (-64749565/4294967296) 1 8 ![60,0,4] ![(9/8000),0,(1/4)] ![(1/16000),1,(1/4)] affine00013
theorem leaf00013_checked : FastNestedCellData.accepts 1 2 4 leaf00013=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8808556443/1000000000000) (2083700525/2147483648) (-64749565/4294967296) 1 8 ![60,0,4] ![(9/8000),0,(1/4)] ![(1/16000),1,(1/4)] 1624891863628463377977578618880000000000 1590518250256346525959025001497616187392 180565142602940635543024697344000000000000 raw00013 affine00013
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00013_raw leaf00013_rectangular
    leaf00013_transform leaf00013_sign leaf00013_log
#print axioms leaf00013_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
