/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00526 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7459022936473476545460043776000000000000 3038950751224907046450458949284599431168 7339415678099220672400064512000000000000))
theorem leaf00526_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7459022936473476545460043776000000000000 3038950751224907046450458949284599431168 7339415678099220672400064512000000000000 raw00526=true := by decide +kernel
#print axioms leaf00526_raw
theorem leaf00526_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00526=true := by decide +kernel
#print axioms leaf00526_rectangular
def affine00526 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00526 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00526_transform : affine00526=(NestedInteger.clearedAll 3 raw00526 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00526_transform
theorem leaf00526_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00526=true := by decide +kernel
#print axioms leaf00526_sign
theorem leaf00526_log : RationalLog.accepts (309367063/1073741824) (-2672278001/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00526_log
def leaf00526 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (51757368783/125000000000) (309367063/1073741824) (-2672278001/4294967296) 2 8 ![60,0,4] ![(3/200),0,(1/16)] ![(1/3200),1,(1/16)] affine00526
theorem leaf00526_checked : FastNestedCellData.accepts 1 2 4 leaf00526=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (51757368783/125000000000) (309367063/1073741824) (-2672278001/4294967296) 2 8 ![60,0,4] ![(3/200),0,(1/16)] ![(1/3200),1,(1/16)] 7459022936473476545460043776000000000000 3038950751224907046450458949284599431168 7339415678099220672400064512000000000000 raw00526 affine00526
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00526_raw leaf00526_rectangular
    leaf00526_transform leaf00526_sign leaf00526_log
#print axioms leaf00526_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
