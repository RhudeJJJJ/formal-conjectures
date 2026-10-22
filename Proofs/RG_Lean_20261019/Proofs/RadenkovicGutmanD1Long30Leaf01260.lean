/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01260 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 3938017090679721716401307648000000000000 4190104836502781106634290675226811301888 1226724481210258453418376953856000000000000))
theorem leaf01260_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 3938017090679721716401307648000000000000 4190104836502781106634290675226811301888 1226724481210258453418376953856000000000000 raw01260=true := by decide +kernel
#print axioms leaf01260_raw
theorem leaf01260_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01260=true := by decide +kernel
#print axioms leaf01260_rectangular
def affine01260 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01260 (IntegerComputedClassCell.leftNumerator ![(25/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(25/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(25/128),0,0] ![(1/128),1,(1/2)]))
theorem leaf01260_transform : affine01260=(NestedInteger.clearedAll 3 raw01260 (IntegerComputedClassCell.leftNumerator ![(25/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(25/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(25/128),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01260_transform
theorem leaf01260_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01260=true := by decide +kernel
#print axioms leaf01260_sign
theorem leaf01260_log : RationalLog.accepts (4554348587/4294967296) (15740671/536870912) 0 8=true := by decide +kernel
#print axioms leaf01260_log
def leaf01260 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (853921337/250000000000) (4554348587/4294967296) (15740671/536870912) 0 8 ![60,0,4] ![(25/128),0,0] ![(1/128),1,(1/2)] affine01260
theorem leaf01260_checked : FastNestedCellData.accepts 1 2 4 leaf01260=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (853921337/250000000000) (4554348587/4294967296) (15740671/536870912) 0 8 ![60,0,4] ![(25/128),0,0] ![(1/128),1,(1/2)] 3938017090679721716401307648000000000000 4190104836502781106634290675226811301888 1226724481210258453418376953856000000000000 raw01260 affine01260
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01260_raw leaf01260_rectangular
    leaf01260_transform leaf01260_sign leaf01260_log
#print axioms leaf01260_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
