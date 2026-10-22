/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00629 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5792426313993310595299934208000000000000 4851937247075562079304479756692379140096 60357940782546528516473618432000000000000))
theorem leaf00629_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5792426313993310595299934208000000000000 4851937247075562079304479756692379140096 60357940782546528516473618432000000000000 raw00629=true := by decide +kernel
#print axioms leaf00629_raw
theorem leaf00629_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00629=true := by decide +kernel
#print axioms leaf00629_rectangular
def affine00629 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00629 (IntegerComputedClassCell.leftNumerator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00629_transform : affine00629=(NestedInteger.clearedAll 3 raw00629 (IntegerComputedClassCell.leftNumerator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00629_transform
theorem leaf00629_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00629=true := by decide +kernel
#print axioms leaf00629_sign
theorem leaf00629_log : RationalLog.accepts (416241673/536870912) (-546516675/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00629_log
def leaf00629 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (40193031639/500000000000) (416241673/536870912) (-546516675/4294967296) 1 8 ![60,0,4] ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)] affine00629
theorem leaf00629_checked : FastNestedCellData.accepts 1 2 4 leaf00629=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (40193031639/500000000000) (416241673/536870912) (-546516675/4294967296) 1 8 ![60,0,4] ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)] 5792426313993310595299934208000000000000 4851937247075562079304479756692379140096 60357940782546528516473618432000000000000 raw00629 affine00629
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00629_raw leaf00629_rectangular
    leaf00629_transform leaf00629_sign leaf00629_log
#print axioms leaf00629_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
