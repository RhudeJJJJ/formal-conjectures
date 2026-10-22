/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01002 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10060114918919978515077005312000000000000 5938235147470211547694488552159546703872 10633450537265359926438395904000000000000))
theorem leaf01002_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10060114918919978515077005312000000000000 5938235147470211547694488552159546703872 10633450537265359926438395904000000000000 raw01002=true := by decide +kernel
#print axioms leaf01002_raw
theorem leaf01002_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01002=true := by decide +kernel
#print axioms leaf01002_rectangular
def affine01002 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01002 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/8)] ![(1/160),1,(1/8)]))
theorem leaf01002_transform : affine01002=(NestedInteger.clearedAll 3 raw01002 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/8)] ![(1/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01002_transform
theorem leaf01002_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01002=true := by decide +kernel
#print axioms leaf01002_sign
theorem leaf01002_log : RationalLog.accepts (203344229/536870912) (-1042450259/2147483648) 2 8=true := by decide +kernel
#print axioms leaf01002_log
def leaf01002 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (139612140167/250000000000) (203344229/536870912) (-1042450259/2147483648) 2 8 ![60,0,4] ![(3/20),0,(1/8)] ![(1/160),1,(1/8)] affine01002
theorem leaf01002_checked : FastNestedCellData.accepts 1 2 4 leaf01002=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (139612140167/250000000000) (203344229/536870912) (-1042450259/2147483648) 2 8 ![60,0,4] ![(3/20),0,(1/8)] ![(1/160),1,(1/8)] 10060114918919978515077005312000000000000 5938235147470211547694488552159546703872 10633450537265359926438395904000000000000 raw01002 affine01002
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01002_raw leaf01002_rectangular
    leaf01002_transform leaf01002_sign leaf01002_log
#print axioms leaf01002_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
