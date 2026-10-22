/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01191 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 6655511035266787753485926400000000000 7891391268238603276841596954941063168 355992365692667340120915968000000000000))
theorem leaf01191_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 6655511035266787753485926400000000000 7891391268238603276841596954941063168 355992365692667340120915968000000000000 raw01191=true := by decide +kernel
#print axioms leaf01191_raw
theorem leaf01191_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01191=true := by decide +kernel
#print axioms leaf01191_rectangular
def affine01191 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01191 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf01191_transform : affine01191=(NestedInteger.clearedAll 3 raw01191 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf01191_transform
theorem leaf01191_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01191=true := by decide +kernel
#print axioms leaf01191_sign
theorem leaf01191_log : RationalLog.accepts (622759065/536870912) (318690937/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01191_log
def leaf01191 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2770913097/125000000000) (622759065/536870912) (318690937/4294967296) 0 8 ![60,0,4] ![(13/32),0,(1/2)] ![(1/32),1,(1/4)] affine01191
theorem leaf01191_checked : FastNestedCellData.accepts 1 2 4 leaf01191=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2770913097/125000000000) (622759065/536870912) (318690937/4294967296) 0 8 ![60,0,4] ![(13/32),0,(1/2)] ![(1/32),1,(1/4)] 6655511035266787753485926400000000000 7891391268238603276841596954941063168 355992365692667340120915968000000000000 raw01191 affine01191
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01191_raw leaf01191_rectangular
    leaf01191_transform leaf01191_sign leaf01191_log
#print axioms leaf01191_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
