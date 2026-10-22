/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00160 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 367152187761431624291459268608000000000000 87982295121956575295796212993152253952 276279655826758730036281344000000000000))
theorem leaf00160_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 367152187761431624291459268608000000000000 87982295121956575295796212993152253952 276279655826758730036281344000000000000 raw00160=true := by decide +kernel
#print axioms leaf00160_raw
theorem leaf00160_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00160=true := by decide +kernel
#print axioms leaf00160_rectangular
def affine00160 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00160 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/2000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00160_transform : affine00160=(NestedInteger.clearedAll 3 raw00160 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/2000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00160_transform
theorem leaf00160_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00160=true := by decide +kernel
#print axioms leaf00160_sign
theorem leaf00160_log : RationalLog.accepts (195157/1073741824) (-9247983699/2147483648) 13 8=true := by decide +kernel
#print axioms leaf00160_log
def leaf00160 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (318453759683/1000000000000) (195157/1073741824) (-9247983699/2147483648) 13 8 ![60,0,4] ![(7/2000),0,0] ![(3/32000),1,(1/16)] affine00160
theorem leaf00160_checked : FastNestedCellData.accepts 1 2 4 leaf00160=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (318453759683/1000000000000) (195157/1073741824) (-9247983699/2147483648) 13 8 ![60,0,4] ![(7/2000),0,0] ![(3/32000),1,(1/16)] 367152187761431624291459268608000000000000 87982295121956575295796212993152253952 276279655826758730036281344000000000000 raw00160 affine00160
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00160_raw leaf00160_rectangular
    leaf00160_transform leaf00160_sign leaf00160_log
#print axioms leaf00160_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
