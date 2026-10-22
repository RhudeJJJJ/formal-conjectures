/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00096 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7026667000419938298188791808000000000000 5929755480146302183522292269486536916992 81078537540301767989948055552000000000000))
theorem leaf00096_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7026667000419938298188791808000000000000 5929755480146302183522292269486536916992 81078537540301767989948055552000000000000 raw00096=true := by decide +kernel
#print axioms leaf00096_raw
theorem leaf00096_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00096=true := by decide +kernel
#print axioms leaf00096_rectangular
def affine00096 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00096 (IntegerComputedClassCell.leftNumerator ![(73/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00096_transform : affine00096=(NestedInteger.clearedAll 3 raw00096 (IntegerComputedClassCell.leftNumerator ![(73/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00096_transform
theorem leaf00096_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00096=true := by decide +kernel
#print axioms leaf00096_sign
theorem leaf00096_log : RationalLog.accepts (422184753/536870912) (-516071831/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00096_log
def leaf00096 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (73135945221/1000000000000) (422184753/536870912) (-516071831/4294967296) 1 8 ![60,0,4] ![(73/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00096
theorem leaf00096_checked : FastNestedCellData.accepts 1 2 4 leaf00096=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (73135945221/1000000000000) (422184753/536870912) (-516071831/4294967296) 1 8 ![60,0,4] ![(73/32000),0,(1/16)] ![(3/32000),1,(1/16)] 7026667000419938298188791808000000000000 5929755480146302183522292269486536916992 81078537540301767989948055552000000000000 raw00096 affine00096
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00096_raw leaf00096_rectangular
    leaf00096_transform leaf00096_sign leaf00096_log
#print axioms leaf00096_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
