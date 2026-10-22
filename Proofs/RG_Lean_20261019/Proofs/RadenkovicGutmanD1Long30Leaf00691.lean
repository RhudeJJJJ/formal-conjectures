/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00691 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11132567212801238749316034592768000000000000 3119468161894520666101966252605584921591808 5168981217771945231509247492096000000000000))
theorem leaf00691_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11132567212801238749316034592768000000000000 3119468161894520666101966252605584921591808 5168981217771945231509247492096000000000000 raw00691=true := by decide +kernel
#print axioms leaf00691_raw
theorem leaf00691_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00691=true := by decide +kernel
#print axioms leaf00691_rectangular
def affine00691 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00691 (IntegerComputedClassCell.leftNumerator ![(179/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(179/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(179/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00691_transform : affine00691=(NestedInteger.clearedAll 3 raw00691 (IntegerComputedClassCell.leftNumerator ![(179/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(179/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(179/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00691_transform
theorem leaf00691_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00691=true := by decide +kernel
#print axioms leaf00691_sign
theorem leaf00691_log : RationalLog.accepts (750545037/4294967296) (-468258705/536870912) 3 8=true := by decide +kernel
#print axioms leaf00691_log
def leaf00691 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (603497677873/1000000000000) (750545037/4294967296) (-468258705/536870912) 3 8 ![60,0,4] ![(179/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00691
theorem leaf00691_checked : FastNestedCellData.accepts 1 2 4 leaf00691=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (603497677873/1000000000000) (750545037/4294967296) (-468258705/536870912) 3 8 ![60,0,4] ![(179/6400),0,(1/16)] ![(3/6400),1,(1/16)] 11132567212801238749316034592768000000000000 3119468161894520666101966252605584921591808 5168981217771945231509247492096000000000000 raw00691 affine00691
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00691_raw leaf00691_rectangular
    leaf00691_transform leaf00691_sign leaf00691_log
#print axioms leaf00691_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
