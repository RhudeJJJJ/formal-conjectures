/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01112 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 43367218323968662196282667827200000000000 51677150716482226006440053357309155344384 274768364956035640533234745344000000000000))
theorem leaf01112_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 43367218323968662196282667827200000000000 51677150716482226006440053357309155344384 274768364956035640533234745344000000000000 raw01112=true := by decide +kernel
#print axioms leaf01112_raw
theorem leaf01112_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01112=true := by decide +kernel
#print axioms leaf01112_rectangular
def affine01112 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01112 (IntegerComputedClassCell.leftNumerator ![(19/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/32),0,(3/4)] ![(1/32),1,(1/8)]))
theorem leaf01112_transform : affine01112=(NestedInteger.clearedAll 3 raw01112 (IntegerComputedClassCell.leftNumerator ![(19/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/32),0,(3/4)] ![(1/32),1,(1/8)])) := by decide +kernel
#print axioms leaf01112_transform
theorem leaf01112_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01112=true := by decide +kernel
#print axioms leaf01112_sign
theorem leaf01112_log : RationalLog.accepts (2153886835/2147483648) (6393659/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01112_log
def leaf01112 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (94037664643/500000000000) (2153886835/2147483648) (6393659/4294967296) 0 8 ![60,0,4] ![(19/32),0,(3/4)] ![(1/32),1,(1/8)] affine01112
theorem leaf01112_checked : FastNestedCellData.accepts 1 2 4 leaf01112=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (94037664643/500000000000) (2153886835/2147483648) (6393659/4294967296) 0 8 ![60,0,4] ![(19/32),0,(3/4)] ![(1/32),1,(1/8)] 43367218323968662196282667827200000000000 51677150716482226006440053357309155344384 274768364956035640533234745344000000000000 raw01112 affine01112
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01112_raw leaf01112_rectangular
    leaf01112_transform leaf01112_sign leaf01112_log
#print axioms leaf01112_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
