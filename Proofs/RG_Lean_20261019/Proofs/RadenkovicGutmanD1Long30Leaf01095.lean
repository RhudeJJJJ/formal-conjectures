/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01095 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1724808729457699070200281825280000000000 1988138092891779212549451014967916494848 8505215437841297061705930506240000000000))
theorem leaf01095_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1724808729457699070200281825280000000000 1988138092891779212549451014967916494848 8505215437841297061705930506240000000000 raw01095=true := by decide +kernel
#print axioms leaf01095_raw
theorem leaf01095_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01095=true := by decide +kernel
#print axioms leaf01095_rectangular
def affine01095 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01095 (IntegerComputedClassCell.leftNumerator ![(1/2),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/2),0,0] ![(1/32),1,(1/2)]))
theorem leaf01095_transform : affine01095=(NestedInteger.clearedAll 3 raw01095 (IntegerComputedClassCell.leftNumerator ![(1/2),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/2),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf01095_transform
theorem leaf01095_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01095=true := by decide +kernel
#print axioms leaf01095_sign
theorem leaf01095_log : RationalLog.accepts (4012698043/4294967296) (-145986183/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01095_log
def leaf01095 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4675103429/20000000000) (4012698043/4294967296) (-145986183/4294967296) 1 8 ![60,0,4] ![(1/2),0,0] ![(1/32),1,(1/2)] affine01095
theorem leaf01095_checked : FastNestedCellData.accepts 1 2 4 leaf01095=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4675103429/20000000000) (4012698043/4294967296) (-145986183/4294967296) 1 8 ![60,0,4] ![(1/2),0,0] ![(1/32),1,(1/2)] 1724808729457699070200281825280000000000 1988138092891779212549451014967916494848 8505215437841297061705930506240000000000 raw01095 affine01095
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01095_raw leaf01095_rectangular
    leaf01095_transform leaf01095_sign leaf01095_log
#print axioms leaf01095_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
