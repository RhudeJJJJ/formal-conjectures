/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00484 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 213103902462517028097372454912000000000000 191883502372145209496398718056203653480448 4152464853205338680320868745216000000000000))
theorem leaf00484_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 213103902462517028097372454912000000000000 191883502372145209496398718056203653480448 4152464853205338680320868745216000000000000 raw00484=true := by decide +kernel
#print axioms leaf00484_raw
theorem leaf00484_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00484=true := by decide +kernel
#print axioms leaf00484_rectangular
def affine00484 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00484 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00484_transform : affine00484=(NestedInteger.clearedAll 3 raw00484 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00484_transform
theorem leaf00484_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00484=true := by decide +kernel
#print axioms leaf00484_sign
theorem leaf00484_log : RationalLog.accepts (1848235989/2147483648) (-322262375/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00484_log
def leaf00484 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (46209542803/1000000000000) (1848235989/2147483648) (-322262375/4294967296) 1 8 ![60,0,4] ![(1/80),0,(1/2)] ![(1/6400),1,(1/2)] affine00484
theorem leaf00484_checked : FastNestedCellData.accepts 1 2 4 leaf00484=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (46209542803/1000000000000) (1848235989/2147483648) (-322262375/4294967296) 1 8 ![60,0,4] ![(1/80),0,(1/2)] ![(1/6400),1,(1/2)] 213103902462517028097372454912000000000000 191883502372145209496398718056203653480448 4152464853205338680320868745216000000000000 raw00484 affine00484
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00484_raw leaf00484_rectangular
    leaf00484_transform leaf00484_sign leaf00484_log
#print axioms leaf00484_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
