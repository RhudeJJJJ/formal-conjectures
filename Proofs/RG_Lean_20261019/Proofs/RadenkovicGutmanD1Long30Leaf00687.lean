/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00687 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3413386863924107267497755934720000000000 1608925817903148606721197916705335017472 4347506447353441278566911180800000000000))
theorem leaf00687_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3413386863924107267497755934720000000000 1608925817903148606721197916705335017472 4347506447353441278566911180800000000000 raw00687=true := by decide +kernel
#print axioms leaf00687_raw
theorem leaf00687_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00687=true := by decide +kernel
#print axioms leaf00687_rectangular
def affine00687 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00687 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00687_transform : affine00687=(NestedInteger.clearedAll 3 raw00687 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00687_transform
theorem leaf00687_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00687=true := by decide +kernel
#print axioms leaf00687_sign
theorem leaf00687_log : RationalLog.accepts (1477625565/4294967296) (-2291381207/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00687_log
def leaf00687 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18504007267/50000000000) (1477625565/4294967296) (-2291381207/4294967296) 2 8 ![60,0,4] ![(11/400),0,(1/8)] ![(3/6400),1,(1/8)] affine00687
theorem leaf00687_checked : FastNestedCellData.accepts 1 2 4 leaf00687=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18504007267/50000000000) (1477625565/4294967296) (-2291381207/4294967296) 2 8 ![60,0,4] ![(11/400),0,(1/8)] ![(3/6400),1,(1/8)] 3413386863924107267497755934720000000000 1608925817903148606721197916705335017472 4347506447353441278566911180800000000000 raw00687 affine00687
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00687_raw leaf00687_rectangular
    leaf00687_transform leaf00687_sign leaf00687_log
#print axioms leaf00687_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
