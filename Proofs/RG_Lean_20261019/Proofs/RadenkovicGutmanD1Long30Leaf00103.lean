/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00103 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 68044488177767733968278808166400000000000 65123411779794109055944816667574637953024 3530969054158220566246994214912000000000000))
theorem leaf00103_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 68044488177767733968278808166400000000000 65123411779794109055944816667574637953024 3530969054158220566246994214912000000000000 raw00103=true := by decide +kernel
#print axioms leaf00103_raw
theorem leaf00103_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00103=true := by decide +kernel
#print axioms leaf00103_rectangular
def affine00103 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00103 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00103_transform : affine00103=(NestedInteger.clearedAll 3 raw00103 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00103_transform
theorem leaf00103_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00103=true := by decide +kernel
#print axioms leaf00103_sign
theorem leaf00103_log : RationalLog.accepts (4036148305/4294967296) (-33368197/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00103_log
def leaf00103 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18443495477/1000000000000) (4036148305/4294967296) (-33368197/1073741824) 1 8 ![60,0,4] ![(19/8000),0,(1/4)] ![(3/32000),1,(1/4)] affine00103
theorem leaf00103_checked : FastNestedCellData.accepts 1 2 4 leaf00103=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18443495477/1000000000000) (4036148305/4294967296) (-33368197/1073741824) 1 8 ![60,0,4] ![(19/8000),0,(1/4)] ![(3/32000),1,(1/4)] 68044488177767733968278808166400000000000 65123411779794109055944816667574637953024 3530969054158220566246994214912000000000000 raw00103 affine00103
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00103_raw leaf00103_rectangular
    leaf00103_transform leaf00103_sign leaf00103_log
#print axioms leaf00103_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
