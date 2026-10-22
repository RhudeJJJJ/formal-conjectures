/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01043 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 464075939742896100321267810304000000000000 383967034196486867263701039547881590095872 953903904241393591331133063168000000000000))
theorem leaf01043_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 464075939742896100321267810304000000000000 383967034196486867263701039547881590095872 953903904241393591331133063168000000000000 raw01043=true := by decide +kernel
#print axioms leaf01043_raw
theorem leaf01043_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01043=true := by decide +kernel
#print axioms leaf01043_rectangular
def affine01043 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01043 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf01043_transform : affine01043=(NestedInteger.clearedAll 3 raw01043 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01043_transform
theorem leaf01043_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01043=true := by decide +kernel
#print axioms leaf01043_sign
theorem leaf01043_log : RationalLog.accepts (1266849891/2147483648) (-1133363183/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01043_log
def leaf01043 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (201260856827/500000000000) (1266849891/2147483648) (-1133363183/4294967296) 1 8 ![60,0,4] ![(19/80),0,(1/4)] ![(3/160),1,(1/4)] affine01043
theorem leaf01043_checked : FastNestedCellData.accepts 1 2 4 leaf01043=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (201260856827/500000000000) (1266849891/2147483648) (-1133363183/4294967296) 1 8 ![60,0,4] ![(19/80),0,(1/4)] ![(3/160),1,(1/4)] 464075939742896100321267810304000000000000 383967034196486867263701039547881590095872 953903904241393591331133063168000000000000 raw01043 affine01043
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01043_raw leaf01043_rectangular
    leaf01043_transform leaf01043_sign leaf01043_log
#print axioms leaf01043_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
