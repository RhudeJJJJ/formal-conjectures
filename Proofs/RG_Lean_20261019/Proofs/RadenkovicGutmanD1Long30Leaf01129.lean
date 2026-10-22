/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01129 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10921982731646223777932928614400000000000 13555128566925300709001729201475208347648 95391710501042757087608700928000000000000))
theorem leaf01129_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10921982731646223777932928614400000000000 13555128566925300709001729201475208347648 95391710501042757087608700928000000000000 raw01129=true := by decide +kernel
#print axioms leaf01129_raw
theorem leaf01129_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01129=true := by decide +kernel
#print axioms leaf01129_rectangular
def affine01129 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01129 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01129_transform : affine01129=(NestedInteger.clearedAll 3 raw01129 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01129_transform
theorem leaf01129_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01129=true := by decide +kernel
#print axioms leaf01129_sign
theorem leaf01129_log : RationalLog.accepts (2333608635/2147483648) (178496863/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01129_log
def leaf01129 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (71049824433/500000000000) (2333608635/2147483648) (178496863/4294967296) 0 8 ![60,0,4] ![(3/4),0,(15/16)] ![(1/16),1,(1/16)] affine01129
theorem leaf01129_checked : FastNestedCellData.accepts 1 2 4 leaf01129=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (71049824433/500000000000) (2333608635/2147483648) (178496863/4294967296) 0 8 ![60,0,4] ![(3/4),0,(15/16)] ![(1/16),1,(1/16)] 10921982731646223777932928614400000000000 13555128566925300709001729201475208347648 95391710501042757087608700928000000000000 raw01129 affine01129
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01129_raw leaf01129_rectangular
    leaf01129_transform leaf01129_sign leaf01129_log
#print axioms leaf01129_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
