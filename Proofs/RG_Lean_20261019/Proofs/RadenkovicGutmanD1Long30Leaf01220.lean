/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01220 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 191113514285796451453243490304000000000000 214846341472305653022164192205106034245632 20737494630472498087679102025728000000000000))
theorem leaf01220_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 191113514285796451453243490304000000000000 214846341472305653022164192205106034245632 20737494630472498087679102025728000000000000 raw01220=true := by decide +kernel
#print axioms leaf01220_raw
theorem leaf01220_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01220=true := by decide +kernel
#print axioms leaf01220_rectangular
def affine01220 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01220 (IntegerComputedClassCell.leftNumerator ![(19/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf01220_transform : affine01220=(NestedInteger.clearedAll 3 raw01220 (IntegerComputedClassCell.leftNumerator ![(19/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf01220_transform
theorem leaf01220_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01220=true := by decide +kernel
#print axioms leaf01220_sign
theorem leaf01220_log : RationalLog.accepts (4778814347/4294967296) (229240723/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01220_log
def leaf01220 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (10360284369/1000000000000) (4778814347/4294967296) (229240723/4294967296) 0 8 ![60,0,4] ![(19/64),0,0] ![(1/64),1,(1/2)] affine01220
theorem leaf01220_checked : FastNestedCellData.accepts 1 2 4 leaf01220=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (10360284369/1000000000000) (4778814347/4294967296) (229240723/4294967296) 0 8 ![60,0,4] ![(19/64),0,0] ![(1/64),1,(1/2)] 191113514285796451453243490304000000000000 214846341472305653022164192205106034245632 20737494630472498087679102025728000000000000 raw01220 affine01220
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01220_raw leaf01220_rectangular
    leaf01220_transform leaf01220_sign leaf01220_log
#print axioms leaf01220_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
