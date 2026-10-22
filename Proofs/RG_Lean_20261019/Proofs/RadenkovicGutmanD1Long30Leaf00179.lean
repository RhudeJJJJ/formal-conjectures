/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00179 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 84835913299312259568238592000000000000 82045259847366143473364565259381112832 5807273316313145316095295488000000000000))
theorem leaf00179_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 84835913299312259568238592000000000000 82045259847366143473364565259381112832 5807273316313145316095295488000000000000 raw00179=true := by decide +kernel
#print axioms leaf00179_raw
theorem leaf00179_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00179=true := by decide +kernel
#print axioms leaf00179_rectangular
def affine00179 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00179 (IntegerComputedClassCell.leftNumerator ![(121/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(121/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(121/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00179_transform : affine00179=(NestedInteger.clearedAll 3 raw00179 (IntegerComputedClassCell.leftNumerator ![(121/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(121/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(121/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00179_transform
theorem leaf00179_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00179=true := by decide +kernel
#print axioms leaf00179_sign
theorem leaf00179_log : RationalLog.accepts (127994367/134217728) (-101956251/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00179_log
def leaf00179 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (14128017639/1000000000000) (127994367/134217728) (-101956251/4294967296) 1 8 ![60,0,4] ![(121/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00179
theorem leaf00179_checked : FastNestedCellData.accepts 1 2 4 leaf00179=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (14128017639/1000000000000) (127994367/134217728) (-101956251/4294967296) 1 8 ![60,0,4] ![(121/32000),0,(1/2)] ![(3/32000),1,(1/2)] 84835913299312259568238592000000000000 82045259847366143473364565259381112832 5807273316313145316095295488000000000000 raw00179 affine00179
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00179_raw leaf00179_rectangular
    leaf00179_transform leaf00179_sign leaf00179_log
#print axioms leaf00179_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
