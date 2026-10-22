/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00222 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 27810977288373894912667549696000000000000 23584263821834397341042645117927342211072 325900149049909976198853689344000000000000))
theorem leaf00222_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 27810977288373894912667549696000000000000 23584263821834397341042645117927342211072 325900149049909976198853689344000000000000 raw00222=true := by decide +kernel
#print axioms leaf00222_raw
theorem leaf00222_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00222=true := by decide +kernel
#print axioms leaf00222_rectangular
def affine00222 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00222 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00222_transform : affine00222=(NestedInteger.clearedAll 3 raw00222 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00222_transform
theorem leaf00222_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00222=true := by decide +kernel
#print axioms leaf00222_sign
theorem leaf00222_log : RationalLog.accepts (3396430119/4294967296) (-252027653/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00222_log
def leaf00222 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18091633197/250000000000) (3396430119/4294967296) (-252027653/2147483648) 1 8 ![60,0,4] ![(37/8000),0,(1/8)] ![(3/32000),1,(1/8)] affine00222
theorem leaf00222_checked : FastNestedCellData.accepts 1 2 4 leaf00222=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18091633197/250000000000) (3396430119/4294967296) (-252027653/2147483648) 1 8 ![60,0,4] ![(37/8000),0,(1/8)] ![(3/32000),1,(1/8)] 27810977288373894912667549696000000000000 23584263821834397341042645117927342211072 325900149049909976198853689344000000000000 raw00222 affine00222
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00222_raw leaf00222_rectangular
    leaf00222_transform leaf00222_sign leaf00222_log
#print axioms leaf00222_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
