/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01278 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1784779847437421911327794790400000000000 1876314796444036266908508221753341771776 775712453307071190379131410841600000000000))
theorem leaf01278_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1784779847437421911327794790400000000000 1876314796444036266908508221753341771776 775712453307071190379131410841600000000000 raw01278=true := by decide +kernel
#print axioms leaf01278_raw
theorem leaf01278_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01278=true := by decide +kernel
#print axioms leaf01278_rectangular
def affine01278 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01278 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/64),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01278_transform : affine01278=(NestedInteger.clearedAll 3 raw01278 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/64),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01278_transform
theorem leaf01278_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01278=true := by decide +kernel
#print axioms leaf01278_sign
theorem leaf01278_log : RationalLog.accepts (4504345509/4294967296) (25554335/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01278_log
def leaf01278 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (483765547/200000000000) (4504345509/4294967296) (25554335/1073741824) 0 8 ![60,0,4] ![(11/64),0,(7/8)] ![(1/128),1,(1/16)] affine01278
theorem leaf01278_checked : FastNestedCellData.accepts 1 2 4 leaf01278=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (483765547/200000000000) (4504345509/4294967296) (25554335/1073741824) 0 8 ![60,0,4] ![(11/64),0,(7/8)] ![(1/128),1,(1/16)] 1784779847437421911327794790400000000000 1876314796444036266908508221753341771776 775712453307071190379131410841600000000000 raw01278 affine01278
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01278_raw leaf01278_rectangular
    leaf01278_transform leaf01278_sign leaf01278_log
#print axioms leaf01278_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
