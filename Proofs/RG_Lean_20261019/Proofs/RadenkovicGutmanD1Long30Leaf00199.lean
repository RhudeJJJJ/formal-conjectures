/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00199 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 14305910237610570980416238387200000000000 13791811946657669879725836404698883555328 889192022971958724318034132992000000000000))
theorem leaf00199_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 14305910237610570980416238387200000000000 13791811946657669879725836404698883555328 889192022971958724318034132992000000000000 raw00199=true := by decide +kernel
#print axioms leaf00199_raw
theorem leaf00199_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00199=true := by decide +kernel
#print axioms leaf00199_rectangular
def affine00199 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00199 (IntegerComputedClassCell.leftNumerator ![(133/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(133/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(133/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00199_transform : affine00199=(NestedInteger.clearedAll 3 raw00199 (IntegerComputedClassCell.leftNumerator ![(133/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(133/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(133/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00199_transform
theorem leaf00199_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00199=true := by decide +kernel
#print axioms leaf00199_sign
theorem leaf00199_log : RationalLog.accepts (2038690405/2147483648) (-111645815/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00199_log
def leaf00199 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15510498959/1000000000000) (2038690405/2147483648) (-111645815/4294967296) 1 8 ![60,0,4] ![(133/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00199
theorem leaf00199_checked : FastNestedCellData.accepts 1 2 4 leaf00199=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15510498959/1000000000000) (2038690405/2147483648) (-111645815/4294967296) 1 8 ![60,0,4] ![(133/32000),0,(1/2)] ![(3/32000),1,(1/2)] 14305910237610570980416238387200000000000 13791811946657669879725836404698883555328 889192022971958724318034132992000000000000 raw00199 affine00199
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00199_raw leaf00199_rectangular
    leaf00199_transform leaf00199_sign leaf00199_log
#print axioms leaf00199_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
