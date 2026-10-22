/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01265 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 6274316278489978552107139072000000000000 6648812176400510346039935849856126418944 2171975242991763220721825742848000000000000))
theorem leaf01265_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 6274316278489978552107139072000000000000 6648812176400510346039935849856126418944 2171975242991763220721825742848000000000000 raw01265=true := by decide +kernel
#print axioms leaf01265_raw
theorem leaf01265_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01265=true := by decide +kernel
#print axioms leaf01265_rectangular
def affine01265 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01265 (IntegerComputedClassCell.leftNumerator ![(3/16),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/16),0,0] ![(1/128),1,(1/2)]))
theorem leaf01265_transform : affine01265=(NestedInteger.clearedAll 3 raw01265 (IntegerComputedClassCell.leftNumerator ![(3/16),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/16),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01265_transform
theorem leaf01265_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01265=true := by decide +kernel
#print axioms leaf01265_sign
theorem leaf01265_log : RationalLog.accepts (4537431639/4294967296) (117933773/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01265_log
def leaf01265 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (3061182303/1000000000000) (4537431639/4294967296) (117933773/4294967296) 0 8 ![60,0,4] ![(3/16),0,0] ![(1/128),1,(1/2)] affine01265
theorem leaf01265_checked : FastNestedCellData.accepts 1 2 4 leaf01265=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (3061182303/1000000000000) (4537431639/4294967296) (117933773/4294967296) 0 8 ![60,0,4] ![(3/16),0,0] ![(1/128),1,(1/2)] 6274316278489978552107139072000000000000 6648812176400510346039935849856126418944 2171975242991763220721825742848000000000000 raw01265 affine01265
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01265_raw leaf01265_rectangular
    leaf01265_transform leaf01265_sign leaf01265_log
#print axioms leaf01265_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
