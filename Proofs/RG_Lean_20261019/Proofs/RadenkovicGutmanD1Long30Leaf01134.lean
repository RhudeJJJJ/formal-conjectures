/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01134 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 596445380341318042665781035008000000000000 748782502766028148995525117332484916248576 5789549072998237268621119193088000000000000))
theorem leaf01134_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 596445380341318042665781035008000000000000 748782502766028148995525117332484916248576 5789549072998237268621119193088000000000000 raw01134=true := by decide +kernel
#print axioms leaf01134_raw
theorem leaf01134_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01134=true := by decide +kernel
#print axioms leaf01134_rectangular
def affine01134 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01134 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01134_transform : affine01134=(NestedInteger.clearedAll 3 raw01134 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01134_transform
theorem leaf01134_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01134=true := by decide +kernel
#print axioms leaf01134_sign
theorem leaf01134_log : RationalLog.accepts (2387221253/2147483648) (28409403/536870912) 0 8=true := by decide +kernel
#print axioms leaf01134_log
def leaf01134 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (129333475427/1000000000000) (2387221253/2147483648) (28409403/536870912) 0 8 ![60,0,4] ![(13/16),0,(15/16)] ![(1/16),1,(1/16)] affine01134
theorem leaf01134_checked : FastNestedCellData.accepts 1 2 4 leaf01134=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (129333475427/1000000000000) (2387221253/2147483648) (28409403/536870912) 0 8 ![60,0,4] ![(13/16),0,(15/16)] ![(1/16),1,(1/16)] 596445380341318042665781035008000000000000 748782502766028148995525117332484916248576 5789549072998237268621119193088000000000000 raw01134 affine01134
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01134_raw leaf01134_rectangular
    leaf01134_transform leaf01134_sign leaf01134_log
#print axioms leaf01134_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
