/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00322 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8193754030814101615149056000000000000 6308869560569430252164068733513367552 54181175867425050159218688000000000000))
theorem leaf00322_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8193754030814101615149056000000000000 6308869560569430252164068733513367552 54181175867425050159218688000000000000 raw00322=true := by decide +kernel
#print axioms leaf00322_raw
theorem leaf00322_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00322=true := by decide +kernel
#print axioms leaf00322_rectangular
def affine00322 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00322 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00322_transform : affine00322=(NestedInteger.clearedAll 3 raw00322 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00322_transform
theorem leaf00322_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00322=true := by decide +kernel
#print axioms leaf00322_sign
theorem leaf00322_log : RationalLog.accepts (46282097/67108864) (-797921045/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00322_log
def leaf00322 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (14555031013/125000000000) (46282097/67108864) (-797921045/4294967296) 1 8 ![60,0,4] ![(3/400),0,(1/8)] ![(1/6400),1,(1/8)] affine00322
theorem leaf00322_checked : FastNestedCellData.accepts 1 2 4 leaf00322=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (14555031013/125000000000) (46282097/67108864) (-797921045/4294967296) 1 8 ![60,0,4] ![(3/400),0,(1/8)] ![(1/6400),1,(1/8)] 8193754030814101615149056000000000000 6308869560569430252164068733513367552 54181175867425050159218688000000000000 raw00322 affine00322
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00322_raw leaf00322_rectangular
    leaf00322_transform leaf00322_sign leaf00322_log
#print axioms leaf00322_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
