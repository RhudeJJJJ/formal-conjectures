/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01238 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 489063628151039564621807616000000000000 536063688039951918517265458282151018496 78982482825992982158865596416000000000000))
theorem leaf01238_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 489063628151039564621807616000000000000 536063688039951918517265458282151018496 78982482825992982158865596416000000000000 raw01238=true := by decide +kernel
#print axioms leaf01238_raw
theorem leaf01238_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01238=true := by decide +kernel
#print axioms leaf01238_rectangular
def affine01238 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01238 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/4),0,(7/8)] ![(1/64),1,(1/16)]))
theorem leaf01238_transform : affine01238=(NestedInteger.clearedAll 3 raw01238 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/4),0,(7/8)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01238_transform
theorem leaf01238_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01238=true := by decide +kernel
#print axioms leaf01238_sign
theorem leaf01238_log : RationalLog.accepts (2337993173/2147483648) (22815989/536870912) 0 8=true := by decide +kernel
#print axioms leaf01238_log
def leaf01238 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (848390157/125000000000) (2337993173/2147483648) (22815989/536870912) 0 8 ![60,0,4] ![(1/4),0,(7/8)] ![(1/64),1,(1/16)] affine01238
theorem leaf01238_checked : FastNestedCellData.accepts 1 2 4 leaf01238=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (848390157/125000000000) (2337993173/2147483648) (22815989/536870912) 0 8 ![60,0,4] ![(1/4),0,(7/8)] ![(1/64),1,(1/16)] 489063628151039564621807616000000000000 536063688039951918517265458282151018496 78982482825992982158865596416000000000000 raw01238 affine01238
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01238_raw leaf01238_rectangular
    leaf01238_transform leaf01238_sign leaf01238_log
#print axioms leaf01238_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
