/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01361 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 122296148601171292979200000000000 122299877999822740533018590445568 2882391656842393130639137177600000000000))
theorem leaf01361_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 122296148601171292979200000000000 122299877999822740533018590445568 2882391656842393130639137177600000000000 raw01361=true := by decide +kernel
#print axioms leaf01361_raw
theorem leaf01361_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01361=true := by decide +kernel
#print axioms leaf01361_rectangular
def affine01361 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01361 (IntegerComputedClassCell.leftNumerator ![(1/256),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/256),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/256),0,0] ![(1/1024),1,1]))
theorem leaf01361_transform : affine01361=(NestedInteger.clearedAll 3 raw01361 (IntegerComputedClassCell.leftNumerator ![(1/256),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/256),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/256),0,0] ![(1/1024),1,1])) := by decide +kernel
#print axioms leaf01361_transform
theorem leaf01361_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01361=true := by decide +kernel
#print axioms leaf01361_sign
theorem leaf01361_log : RationalLog.accepts (536887261/536870912) (65395/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01361_log
def leaf01361 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4243/100000000000) (536887261/536870912) (65395/4294967296) 0 8 ![60,0,4] ![(1/256),0,0] ![(1/1024),1,1] affine01361
theorem leaf01361_checked : FastNestedCellData.accepts 1 2 4 leaf01361=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4243/100000000000) (536887261/536870912) (65395/4294967296) 0 8 ![60,0,4] ![(1/256),0,0] ![(1/1024),1,1] 122296148601171292979200000000000 122299877999822740533018590445568 2882391656842393130639137177600000000000 raw01361 affine01361
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01361_raw leaf01361_rectangular
    leaf01361_transform leaf01361_sign leaf01361_log
#print axioms leaf01361_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
