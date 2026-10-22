/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01235 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 489063856429497476777508864000000000000 536063950948881544895566654730007478272 78982484696066851550556848128000000000000))
theorem leaf01235_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 489063856429497476777508864000000000000 536063950948881544895566654730007478272 78982484696066851550556848128000000000000 raw01235=true := by decide +kernel
#print axioms leaf01235_raw
theorem leaf01235_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01235=true := by decide +kernel
#print axioms leaf01235_rectangular
def affine01235 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01235 (IntegerComputedClassCell.leftNumerator ![(1/4),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/4),0,0] ![(1/64),1,(1/2)]))
theorem leaf01235_transform : affine01235=(NestedInteger.clearedAll 3 raw01235 (IntegerComputedClassCell.leftNumerator ![(1/4),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/4),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf01235_transform
theorem leaf01235_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01235=true := by decide +kernel
#print axioms leaf01235_sign
theorem leaf01235_log : RationalLog.accepts (2337993221/2147483648) (45631989/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01235_log
def leaf01235 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (848390553/125000000000) (2337993221/2147483648) (45631989/1073741824) 0 8 ![60,0,4] ![(1/4),0,0] ![(1/64),1,(1/2)] affine01235
theorem leaf01235_checked : FastNestedCellData.accepts 1 2 4 leaf01235=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (848390553/125000000000) (2337993221/2147483648) (45631989/1073741824) 0 8 ![60,0,4] ![(1/4),0,0] ![(1/64),1,(1/2)] 489063856429497476777508864000000000000 536063950948881544895566654730007478272 78982484696066851550556848128000000000000 raw01235 affine01235
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01235_raw leaf01235_rectangular
    leaf01235_transform leaf01235_sign leaf01235_log
#print axioms leaf01235_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
