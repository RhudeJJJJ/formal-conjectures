/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00919 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4415194943952209014486198124544000000000000 2945086939955207292525895173845944897634304 12304612988967530351362631008256000000000000))
theorem leaf00919_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4415194943952209014486198124544000000000000 2945086939955207292525895173845944897634304 12304612988967530351362631008256000000000000 raw00919=true := by decide +kernel
#print axioms leaf00919_raw
theorem leaf00919_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00919=true := by decide +kernel
#print axioms leaf00919_rectangular
def affine00919 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00919 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00919_transform : affine00919=(NestedInteger.clearedAll 3 raw00919 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00919_transform
theorem leaf00919_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00919=true := by decide +kernel
#print axioms leaf00919_sign
theorem leaf00919_log : RationalLog.accepts (2311611029/4294967296) (-1330364533/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00919_log
def leaf00919 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (239348197509/1000000000000) (2311611029/4294967296) (-1330364533/4294967296) 1 8 ![60,0,4] ![(3/40),0,(1/2)] ![(1/320),1,(1/2)] affine00919
theorem leaf00919_checked : FastNestedCellData.accepts 1 2 4 leaf00919=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (239348197509/1000000000000) (2311611029/4294967296) (-1330364533/4294967296) 1 8 ![60,0,4] ![(3/40),0,(1/2)] ![(1/320),1,(1/2)] 4415194943952209014486198124544000000000000 2945086939955207292525895173845944897634304 12304612988967530351362631008256000000000000 raw00919 affine00919
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00919_raw leaf00919_rectangular
    leaf00919_transform leaf00919_sign leaf00919_log
#print axioms leaf00919_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
