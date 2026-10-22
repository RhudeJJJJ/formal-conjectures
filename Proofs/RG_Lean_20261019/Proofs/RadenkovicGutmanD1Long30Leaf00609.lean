/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00609 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 34011931732679702042346782720000000000 28864776584299567019783635502572240896 391378201170924196319692062720000000000))
theorem leaf00609_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 34011931732679702042346782720000000000 28864776584299567019783635502572240896 391378201170924196319692062720000000000 raw00609=true := by decide +kernel
#print axioms leaf00609_raw
theorem leaf00609_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00609=true := by decide +kernel
#print axioms leaf00609_rectangular
def affine00609 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00609 (IntegerComputedClassCell.leftNumerator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00609_transform : affine00609=(NestedInteger.clearedAll 3 raw00609 (IntegerComputedClassCell.leftNumerator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00609_transform
theorem leaf00609_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00609=true := by decide +kernel
#print axioms leaf00609_sign
theorem leaf00609_log : RationalLog.accepts (848658449/1073741824) (-505191379/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00609_log
def leaf00609 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1475032411/20000000000) (848658449/1073741824) (-505191379/4294967296) 1 8 ![60,0,4] ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)] affine00609
theorem leaf00609_checked : FastNestedCellData.accepts 1 2 4 leaf00609=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1475032411/20000000000) (848658449/1073741824) (-505191379/4294967296) 1 8 ![60,0,4] ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)] 34011931732679702042346782720000000000 28864776584299567019783635502572240896 391378201170924196319692062720000000000 raw00609 affine00609
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00609_raw leaf00609_rectangular
    leaf00609_transform leaf00609_sign leaf00609_log
#print axioms leaf00609_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
