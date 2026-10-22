/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01044 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 96982015515912286373878431744000000000000 81344867693225805997154380281548076220416 241756800871835820017022140416000000000000))
theorem leaf01044_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 96982015515912286373878431744000000000000 81344867693225805997154380281548076220416 241756800871835820017022140416000000000000 raw01044=true := by decide +kernel
#print axioms leaf01044_raw
theorem leaf01044_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01044=true := by decide +kernel
#print axioms leaf01044_rectangular
def affine01044 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01044 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf01044_transform : affine01044=(NestedInteger.clearedAll 3 raw01044 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01044_transform
theorem leaf01044_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01044=true := by decide +kernel
#print axioms leaf01044_sign
theorem leaf01044_log : RationalLog.accepts (673873411/1073741824) (-1000432315/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01044_log
def leaf01044 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (168236979063/500000000000) (673873411/1073741824) (-1000432315/4294967296) 1 8 ![60,0,4] ![(19/80),0,(1/2)] ![(3/160),1,(1/2)] affine01044
theorem leaf01044_checked : FastNestedCellData.accepts 1 2 4 leaf01044=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (168236979063/500000000000) (673873411/1073741824) (-1000432315/4294967296) 1 8 ![60,0,4] ![(19/80),0,(1/2)] ![(3/160),1,(1/2)] 96982015515912286373878431744000000000000 81344867693225805997154380281548076220416 241756800871835820017022140416000000000000 raw01044 affine01044
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01044_raw leaf01044_rectangular
    leaf01044_transform leaf01044_sign leaf01044_log
#print axioms leaf01044_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
