/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00475 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 168884433356637712740642088550400000000000 878765910907151643093257350638622212096 1199812316699181043677134848000000000000))
theorem leaf00475_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 168884433356637712740642088550400000000000 878765910907151643093257350638622212096 1199812316699181043677134848000000000000 raw00475=true := by decide +kernel
#print axioms leaf00475_raw
theorem leaf00475_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00475=true := by decide +kernel
#print axioms leaf00475_rectangular
def affine00475 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00475 (IntegerComputedClassCell.leftNumerator ![(79/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00475_transform : affine00475=(NestedInteger.clearedAll 3 raw00475 (IntegerComputedClassCell.leftNumerator ![(79/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00475_transform
theorem leaf00475_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00475=true := by decide +kernel
#print axioms leaf00475_sign
theorem leaf00475_log : RationalLog.accepts (3225005/1073741824) (-6236260845/2147483648) 9 8=true := by decide +kernel
#print axioms leaf00475_log
def leaf00475 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (732419478177/1000000000000) (3225005/1073741824) (-6236260845/2147483648) 9 8 ![60,0,4] ![(79/6400),0,0] ![(1/6400),1,(1/16)] affine00475
theorem leaf00475_checked : FastNestedCellData.accepts 1 2 4 leaf00475=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (732419478177/1000000000000) (3225005/1073741824) (-6236260845/2147483648) 9 8 ![60,0,4] ![(79/6400),0,0] ![(1/6400),1,(1/16)] 168884433356637712740642088550400000000000 878765910907151643093257350638622212096 1199812316699181043677134848000000000000 raw00475 affine00475
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00475_raw leaf00475_rectangular
    leaf00475_transform leaf00475_sign leaf00475_log
#print axioms leaf00475_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
