/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00035 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 247263466596295004101361532928000000000000 238848674513976059721001824657250759737344 17818970314355726622477850247168000000000000))
theorem leaf00035_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 247263466596295004101361532928000000000000 238848674513976059721001824657250759737344 17818970314355726622477850247168000000000000 raw00035=true := by decide +kernel
#print axioms leaf00035_raw
theorem leaf00035_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00035=true := by decide +kernel
#print axioms leaf00035_rectangular
def affine00035 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00035 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/2)] ![(3/8000),1,(1/2)]))
theorem leaf00035_transform : affine00035=(NestedInteger.clearedAll 3 raw00035 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/2)] ![(3/8000),1,(1/2)])) := by decide +kernel
#print axioms leaf00035_transform
theorem leaf00035_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00035=true := by decide +kernel
#print axioms leaf00035_sign
theorem leaf00035_log : RationalLog.accepts (4093926601/4294967296) (-25737269/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00035_log
def leaf00035 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (13404179383/1000000000000) (4093926601/4294967296) (-25737269/1073741824) 1 8 ![52,0,4] ![(7/2000),0,(1/2)] ![(3/8000),1,(1/2)] affine00035
theorem leaf00035_checked : FastNestedCellData.accepts 1 0 4 leaf00035=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (13404179383/1000000000000) (4093926601/4294967296) (-25737269/1073741824) 1 8 ![52,0,4] ![(7/2000),0,(1/2)] ![(3/8000),1,(1/2)] 247263466596295004101361532928000000000000 238848674513976059721001824657250759737344 17818970314355726622477850247168000000000000 raw00035 affine00035
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00035_raw leaf00035_rectangular
    leaf00035_transform leaf00035_sign leaf00035_log
#print axioms leaf00035_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
