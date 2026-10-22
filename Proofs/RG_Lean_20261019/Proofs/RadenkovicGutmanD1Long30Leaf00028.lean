/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00028 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2950492409528232205633978368000000000000 2878657357496168804018024889027391389696 281212888493985471793796743168000000000000))
theorem leaf00028_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2950492409528232205633978368000000000000 2878657357496168804018024889027391389696 281212888493985471793796743168000000000000 raw00028=true := by decide +kernel
#print axioms leaf00028_raw
theorem leaf00028_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00028=true := by decide +kernel
#print axioms leaf00028_rectangular
def affine00028 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00028 (IntegerComputedClassCell.leftNumerator ![(21/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/16000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00028_transform : affine00028=(NestedInteger.clearedAll 3 raw00028 (IntegerComputedClassCell.leftNumerator ![(21/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/16000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00028_transform
theorem leaf00028_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00028=true := by decide +kernel
#print axioms leaf00028_sign
theorem leaf00028_log : RationalLog.accepts (518492237/536870912) (-18700631/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00028_log
def leaf00028 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10236576897/1000000000000) (518492237/536870912) (-18700631/1073741824) 1 8 ![60,0,4] ![(21/16000),0,(1/4)] ![(1/16000),1,(1/4)] affine00028
theorem leaf00028_checked : FastNestedCellData.accepts 1 2 4 leaf00028=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10236576897/1000000000000) (518492237/536870912) (-18700631/1073741824) 1 8 ![60,0,4] ![(21/16000),0,(1/4)] ![(1/16000),1,(1/4)] 2950492409528232205633978368000000000000 2878657357496168804018024889027391389696 281212888493985471793796743168000000000000 raw00028 affine00028
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00028_raw leaf00028_rectangular
    leaf00028_transform leaf00028_sign leaf00028_log
#print axioms leaf00028_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
