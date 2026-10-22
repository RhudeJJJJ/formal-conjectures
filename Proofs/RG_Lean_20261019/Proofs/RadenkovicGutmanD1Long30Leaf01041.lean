/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01041 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 86455154990249953962859325030400000000000 70663266960422405537269669903922551062528 150772640587843719541294314291200000000000))
theorem leaf01041_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 86455154990249953962859325030400000000000 70663266960422405537269669903922551062528 150772640587843719541294314291200000000000 raw01041=true := by decide +kernel
#print axioms leaf01041_raw
theorem leaf01041_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01041=true := by decide +kernel
#print axioms leaf01041_rectangular
def affine01041 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01041 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/16)] ![(3/160),1,(1/16)]))
theorem leaf01041_transform : affine01041=(NestedInteger.clearedAll 3 raw01041 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/16)] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01041_transform
theorem leaf01041_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01041=true := by decide +kernel
#print axioms leaf01041_sign
theorem leaf01041_log : RationalLog.accepts (1195108069/2147483648) (-1258554613/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01041_log
def leaf01041 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (93734866863/200000000000) (1195108069/2147483648) (-1258554613/4294967296) 1 8 ![60,0,4] ![(19/80),0,(1/16)] ![(3/160),1,(1/16)] affine01041
theorem leaf01041_checked : FastNestedCellData.accepts 1 2 4 leaf01041=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (93734866863/200000000000) (1195108069/2147483648) (-1258554613/4294967296) 1 8 ![60,0,4] ![(19/80),0,(1/16)] ![(3/160),1,(1/16)] 86455154990249953962859325030400000000000 70663266960422405537269669903922551062528 150772640587843719541294314291200000000000 raw01041 affine01041
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01041_raw leaf01041_rectangular
    leaf01041_transform leaf01041_sign leaf01041_log
#print axioms leaf01041_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
