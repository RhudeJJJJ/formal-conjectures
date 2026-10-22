/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00621 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 388160577720320521927426918318080000000000 125730449535747572171544246157731799498752 239005974123370768960917078016000000000000))
theorem leaf00621_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 388160577720320521927426918318080000000000 125730449535747572171544246157731799498752 239005974123370768960917078016000000000000 raw00621=true := by decide +kernel
#print axioms leaf00621_raw
theorem leaf00621_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00621=true := by decide +kernel
#print axioms leaf00621_rectangular
def affine00621 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00621 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00621_transform : affine00621=(NestedInteger.clearedAll 3 raw00621 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00621_transform
theorem leaf00621_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00621=true := by decide +kernel
#print axioms leaf00621_sign
theorem leaf00621_log : RationalLog.accepts (911629825/4294967296) (-3328525041/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00621_log
def leaf00621 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (526055677047/1000000000000) (911629825/4294967296) (-3328525041/4294967296) 3 8 ![60,0,4] ![(137/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00621
theorem leaf00621_checked : FastNestedCellData.accepts 1 2 4 leaf00621=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (526055677047/1000000000000) (911629825/4294967296) (-3328525041/4294967296) 3 8 ![60,0,4] ![(137/6400),0,(1/16)] ![(3/6400),1,(1/16)] 388160577720320521927426918318080000000000 125730449535747572171544246157731799498752 239005974123370768960917078016000000000000 raw00621 affine00621
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00621_raw leaf00621_rectangular
    leaf00621_transform leaf00621_sign leaf00621_log
#print axioms leaf00621_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
