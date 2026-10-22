/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01360 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 14289770296699104159334400000000000 14290451003076898975536675771383808 184476228013643567747197776691200000000000))
theorem leaf01360_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 14289770296699104159334400000000000 14290451003076898975536675771383808 184476228013643567747197776691200000000000 raw01360=true := by decide +kernel
#print axioms leaf01360_raw
theorem leaf01360_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01360=true := by decide +kernel
#print axioms leaf01360_rectangular
def affine01360 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01360 (IntegerComputedClassCell.leftNumerator ![(5/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(5/1024),0,0] ![(1/1024),1,1]))
theorem leaf01360_transform : affine01360=(NestedInteger.clearedAll 3 raw01360 (IntegerComputedClassCell.leftNumerator ![(5/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(5/1024),0,0] ![(1/1024),1,1])) := by decide +kernel
#print axioms leaf01360_transform
theorem leaf01360_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01360=true := by decide +kernel
#print axioms leaf01360_sign
theorem leaf01360_log : RationalLog.accepts (2147585779/2147483648) (6383/268435456) 0 8=true := by decide +kernel
#print axioms leaf01360_log
def leaf01360 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (15493/200000000000) (2147585779/2147483648) (6383/268435456) 0 8 ![60,0,4] ![(5/1024),0,0] ![(1/1024),1,1] affine01360
theorem leaf01360_checked : FastNestedCellData.accepts 1 2 4 leaf01360=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (15493/200000000000) (2147585779/2147483648) (6383/268435456) 0 8 ![60,0,4] ![(5/1024),0,0] ![(1/1024),1,1] 14289770296699104159334400000000000 14290451003076898975536675771383808 184476228013643567747197776691200000000000 raw01360 affine01360
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01360_raw leaf01360_rectangular
    leaf01360_transform leaf01360_sign leaf01360_log
#print axioms leaf01360_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
