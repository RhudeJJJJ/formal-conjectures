/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01122 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2903271618838307174988768083968000000000000 3554113952233600379688540355030003581190144 22582051937629937609386101833728000000000000))
theorem leaf01122_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2903271618838307174988768083968000000000000 3554113952233600379688540355030003581190144 22582051937629937609386101833728000000000000 raw01122=true := by decide +kernel
#print axioms leaf01122_raw
theorem leaf01122_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01122=true := by decide +kernel
#print axioms leaf01122_rectangular
def affine01122 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01122 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/16),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01122_transform : affine01122=(NestedInteger.clearedAll 3 raw01122 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/16),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01122_transform
theorem leaf01122_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01122=true := by decide +kernel
#print axioms leaf01122_sign
theorem leaf01122_log : RationalLog.accepts (4542815141/4294967296) (7530011/268435456) 0 8=true := by decide +kernel
#print axioms leaf01122_log
def leaf01122 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (157386669823/1000000000000) (4542815141/4294967296) (7530011/268435456) 0 8 ![60,0,4] ![(11/16),0,(3/4)] ![(1/16),1,(1/8)] affine01122
theorem leaf01122_checked : FastNestedCellData.accepts 1 2 4 leaf01122=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (157386669823/1000000000000) (4542815141/4294967296) (7530011/268435456) 0 8 ![60,0,4] ![(11/16),0,(3/4)] ![(1/16),1,(1/8)] 2903271618838307174988768083968000000000000 3554113952233600379688540355030003581190144 22582051937629937609386101833728000000000000 raw01122 affine01122
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01122_raw leaf01122_rectangular
    leaf01122_transform leaf01122_sign leaf01122_log
#print axioms leaf01122_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
