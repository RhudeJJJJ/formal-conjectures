/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00835 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 157796621545611550913042841600000000000 13697574137369794813286511366799097856 15637442469098022108554854400000000000))
theorem leaf00835_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 157796621545611550913042841600000000000 13697574137369794813286511366799097856 15637442469098022108554854400000000000 raw00835=true := by decide +kernel
#print axioms leaf00835_raw
theorem leaf00835_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00835=true := by decide +kernel
#print axioms leaf00835_rectangular
def affine00835 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00835 (IntegerComputedClassCell.leftNumerator ![(157/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(157/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(157/3200),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00835_transform : affine00835=(NestedInteger.clearedAll 3 raw00835 (IntegerComputedClassCell.leftNumerator ![(157/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(157/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(157/3200),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00835_transform
theorem leaf00835_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00835=true := by decide +kernel
#print axioms leaf00835_sign
theorem leaf00835_log : RationalLog.accepts (49684991/1073741824) (-1649912785/1073741824) 5 8=true := by decide +kernel
#print axioms leaf00835_log
def leaf00835 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10949340153/12500000000) (49684991/1073741824) (-1649912785/1073741824) 5 8 ![60,0,4] ![(157/3200),0,0] ![(3/3200),1,(1/16)] affine00835
theorem leaf00835_checked : FastNestedCellData.accepts 1 2 4 leaf00835=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10949340153/12500000000) (49684991/1073741824) (-1649912785/1073741824) 5 8 ![60,0,4] ![(157/3200),0,0] ![(3/3200),1,(1/16)] 157796621545611550913042841600000000000 13697574137369794813286511366799097856 15637442469098022108554854400000000000 raw00835 affine00835
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00835_raw leaf00835_rectangular
    leaf00835_transform leaf00835_sign leaf00835_log
#print axioms leaf00835_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
