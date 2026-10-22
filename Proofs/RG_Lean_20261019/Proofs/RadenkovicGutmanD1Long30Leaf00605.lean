/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00605 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 770474008590098501058906659225600000000000 11273267169428189498405661591537960615936 13495268628823306819545858048000000000000))
theorem leaf00605_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 770474008590098501058906659225600000000000 11273267169428189498405661591537960615936 13495268628823306819545858048000000000000 raw00605=true := by decide +kernel
#print axioms leaf00605_raw
theorem leaf00605_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00605=true := by decide +kernel
#print axioms leaf00605_rectangular
def affine00605 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00605 (IntegerComputedClassCell.leftNumerator ![(1/50),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/50),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00605_transform : affine00605=(NestedInteger.clearedAll 3 raw00605 (IntegerComputedClassCell.leftNumerator ![(1/50),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/50),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00605_transform
theorem leaf00605_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00605=true := by decide +kernel
#print axioms leaf00605_sign
theorem leaf00605_log : RationalLog.accepts (17119965/2147483648) (-5188113077/2147483648) 7 8=true := by decide +kernel
#print axioms leaf00605_log
def leaf00605 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (835349593957/1000000000000) (17119965/2147483648) (-5188113077/2147483648) 7 8 ![60,0,4] ![(1/50),0,0] ![(3/6400),1,(1/16)] affine00605
theorem leaf00605_checked : FastNestedCellData.accepts 1 2 4 leaf00605=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (835349593957/1000000000000) (17119965/2147483648) (-5188113077/2147483648) 7 8 ![60,0,4] ![(1/50),0,0] ![(3/6400),1,(1/16)] 770474008590098501058906659225600000000000 11273267169428189498405661591537960615936 13495268628823306819545858048000000000000 raw00605 affine00605
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00605_raw leaf00605_rectangular
    leaf00605_transform leaf00605_sign leaf00605_log
#print axioms leaf00605_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
