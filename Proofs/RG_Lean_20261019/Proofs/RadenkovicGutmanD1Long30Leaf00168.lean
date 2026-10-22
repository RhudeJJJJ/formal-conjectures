/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00168 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 511121216137766954454904471552000000000000 479062980367878232535058761555011392503808 17289738549324546986180308107264000000000000))
theorem leaf00168_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 511121216137766954454904471552000000000000 479062980367878232535058761555011392503808 17289738549324546986180308107264000000000000 raw00168=true := by decide +kernel
#print axioms leaf00168_raw
theorem leaf00168_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00168=true := by decide +kernel
#print axioms leaf00168_rectangular
def affine00168 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00168 (IntegerComputedClassCell.leftNumerator ![(23/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/6400),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00168_transform : affine00168=(NestedInteger.clearedAll 3 raw00168 (IntegerComputedClassCell.leftNumerator ![(23/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/6400),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00168_transform
theorem leaf00168_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00168=true := by decide +kernel
#print axioms leaf00168_sign
theorem leaf00168_log : RationalLog.accepts (3917047647/4294967296) (-12362223/268435456) 1 8=true := by decide +kernel
#print axioms leaf00168_log
def leaf00168 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (27707936647/1000000000000) (3917047647/4294967296) (-12362223/268435456) 1 8 ![60,0,4] ![(23/6400),0,(1/4)] ![(3/32000),1,(1/4)] affine00168
theorem leaf00168_checked : FastNestedCellData.accepts 1 2 4 leaf00168=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (27707936647/1000000000000) (3917047647/4294967296) (-12362223/268435456) 1 8 ![60,0,4] ![(23/6400),0,(1/4)] ![(3/32000),1,(1/4)] 511121216137766954454904471552000000000000 479062980367878232535058761555011392503808 17289738549324546986180308107264000000000000 raw00168 affine00168
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00168_raw leaf00168_rectangular
    leaf00168_transform leaf00168_sign leaf00168_log
#print axioms leaf00168_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
