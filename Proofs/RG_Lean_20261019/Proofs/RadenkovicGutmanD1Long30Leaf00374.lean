/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00374 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1552312734387646370153706291200000000000 1436265313451798244326504713885461774336 42669267075302038025641603891200000000000))
theorem leaf00374_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1552312734387646370153706291200000000000 1436265313451798244326504713885461774336 42669267075302038025641603891200000000000 raw00374=true := by decide +kernel
#print axioms leaf00374_raw
theorem leaf00374_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00374=true := by decide +kernel
#print axioms leaf00374_rectangular
def affine00374 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00374 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00374_transform : affine00374=(NestedInteger.clearedAll 3 raw00374 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00374_transform
theorem leaf00374_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00374=true := by decide +kernel
#print axioms leaf00374_sign
theorem leaf00374_log : RationalLog.accepts (3844478421/4294967296) (-118977053/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00374_log
def leaf00374 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1683020839/50000000000) (3844478421/4294967296) (-118977053/2147483648) 1 8 ![60,0,4] ![(29/3200),0,(1/2)] ![(1/6400),1,(1/2)] affine00374
theorem leaf00374_checked : FastNestedCellData.accepts 1 2 4 leaf00374=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1683020839/50000000000) (3844478421/4294967296) (-118977053/2147483648) 1 8 ![60,0,4] ![(29/3200),0,(1/2)] ![(1/6400),1,(1/2)] 1552312734387646370153706291200000000000 1436265313451798244326504713885461774336 42669267075302038025641603891200000000000 raw00374 affine00374
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00374_raw leaf00374_rectangular
    leaf00374_transform leaf00374_sign leaf00374_log
#print axioms leaf00374_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
