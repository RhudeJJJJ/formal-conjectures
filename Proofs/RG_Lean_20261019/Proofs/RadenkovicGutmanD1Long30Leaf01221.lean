/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01221 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 995381742630596529023352832000000000000 1118989986639173301949812569027559555072 108007775960284067462652100608000000000000))
theorem leaf01221_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 995381742630596529023352832000000000000 1118989986639173301949812569027559555072 108007775960284067462652100608000000000000 raw01221=true := by decide +kernel
#print axioms leaf01221_raw
theorem leaf01221_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01221=true := by decide +kernel
#print axioms leaf01221_rectangular
def affine01221 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01221 (IntegerComputedClassCell.leftNumerator ![(19/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/64),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf01221_transform : affine01221=(NestedInteger.clearedAll 3 raw01221 (IntegerComputedClassCell.leftNumerator ![(19/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/64),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf01221_transform
theorem leaf01221_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01221=true := by decide +kernel
#print axioms leaf01221_sign
theorem leaf01221_log : RationalLog.accepts (597351753/536870912) (229240577/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01221_log
def leaf01221 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (10360272459/1000000000000) (597351753/536870912) (229240577/4294967296) 0 8 ![60,0,4] ![(19/64),0,(1/2)] ![(1/64),1,(1/4)] affine01221
theorem leaf01221_checked : FastNestedCellData.accepts 1 2 4 leaf01221=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (10360272459/1000000000000) (597351753/536870912) (229240577/4294967296) 0 8 ![60,0,4] ![(19/64),0,(1/2)] ![(1/64),1,(1/4)] 995381742630596529023352832000000000000 1118989986639173301949812569027559555072 108007775960284067462652100608000000000000 raw01221 affine01221
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01221_raw leaf01221_rectangular
    leaf01221_transform leaf01221_sign leaf01221_log
#print axioms leaf01221_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
