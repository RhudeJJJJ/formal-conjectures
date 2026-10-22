/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01119 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 199152712987564901133516275712000000000000 238641165706068378425983529001137347756032 1381525401786274694120484110336000000000000))
theorem leaf01119_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 199152712987564901133516275712000000000000 238641165706068378425983529001137347756032 1381525401786274694120484110336000000000000 raw01119=true := by decide +kernel
#print axioms leaf01119_raw
theorem leaf01119_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01119=true := by decide +kernel
#print axioms leaf01119_rectangular
def affine01119 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01119 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/8),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01119_transform : affine01119=(NestedInteger.clearedAll 3 raw01119 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/8),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01119_transform
theorem leaf01119_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01119=true := by decide +kernel
#print axioms leaf01119_sign
theorem leaf01119_log : RationalLog.accepts (2194260619/2147483648) (11568699/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01119_log
def leaf01119 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (86368721631/500000000000) (2194260619/2147483648) (11568699/1073741824) 0 8 ![60,0,4] ![(5/8),0,(15/16)] ![(1/16),1,(1/16)] affine01119
theorem leaf01119_checked : FastNestedCellData.accepts 1 2 4 leaf01119=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (86368721631/500000000000) (2194260619/2147483648) (11568699/1073741824) 0 8 ![60,0,4] ![(5/8),0,(15/16)] ![(1/16),1,(1/16)] 199152712987564901133516275712000000000000 238641165706068378425983529001137347756032 1381525401786274694120484110336000000000000 raw01119 affine01119
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01119_raw leaf01119_rectangular
    leaf01119_transform leaf01119_sign leaf01119_log
#print axioms leaf01119_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
