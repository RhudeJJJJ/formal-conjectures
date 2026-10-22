/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00743 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 42538962679690282893966395310080000000000 26734889634039707564703946923301926862848 115934107427932132249536823296000000000000))
theorem leaf00743_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 42538962679690282893966395310080000000000 26734889634039707564703946923301926862848 115934107427932132249536823296000000000000 raw00743=true := by decide +kernel
#print axioms leaf00743_raw
theorem leaf00743_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00743=true := by decide +kernel
#print axioms leaf00743_rectangular
def affine00743 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00743 (IntegerComputedClassCell.leftNumerator ![(209/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(209/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(209/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00743_transform : affine00743=(NestedInteger.clearedAll 3 raw00743 (IntegerComputedClassCell.leftNumerator ![(209/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(209/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(209/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00743_transform
theorem leaf00743_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00743=true := by decide +kernel
#print axioms leaf00743_sign
theorem leaf00743_log : RationalLog.accepts (1096738225/2147483648) (-180376883/536870912) 1 8=true := by decide +kernel
#print axioms leaf00743_log
def leaf00743 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (230604178763/1000000000000) (1096738225/2147483648) (-180376883/536870912) 1 8 ![60,0,4] ![(209/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00743
theorem leaf00743_checked : FastNestedCellData.accepts 1 2 4 leaf00743=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (230604178763/1000000000000) (1096738225/2147483648) (-180376883/536870912) 1 8 ![60,0,4] ![(209/6400),0,(1/4)] ![(3/6400),1,(1/4)] 42538962679690282893966395310080000000000 26734889634039707564703946923301926862848 115934107427932132249536823296000000000000 raw00743 affine00743
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00743_raw leaf00743_rectangular
    leaf00743_transform leaf00743_sign leaf00743_log
#print axioms leaf00743_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
