/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01335 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 5314009514288286095091171328000000000000 5382530228347075503849368922532947689472 18684602901886604234313626025984000000000000))
theorem leaf01335_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 5314009514288286095091171328000000000000 5382530228347075503849368922532947689472 18684602901886604234313626025984000000000000 raw01335=true := by decide +kernel
#print axioms leaf01335_raw
theorem leaf01335_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01335=true := by decide +kernel
#print axioms leaf01335_rectangular
def affine01335 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01335 (IntegerComputedClassCell.leftNumerator ![(21/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(21/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(21/256),0,0] ![(1/256),1,1]))
theorem leaf01335_transform : affine01335=(NestedInteger.clearedAll 3 raw01335 (IntegerComputedClassCell.leftNumerator ![(21/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(21/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(21/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01335_transform
theorem leaf01335_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01335=true := by decide +kernel
#print axioms leaf01335_sign
theorem leaf01335_log : RationalLog.accepts (4349095263/4294967296) (26894863/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01335_log
def leaf01335 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (288073033/1000000000000) (4349095263/4294967296) (26894863/4294967296) 0 8 ![60,0,4] ![(21/256),0,0] ![(1/256),1,1] affine01335
theorem leaf01335_checked : FastNestedCellData.accepts 1 2 4 leaf01335=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (288073033/1000000000000) (4349095263/4294967296) (26894863/4294967296) 0 8 ![60,0,4] ![(21/256),0,0] ![(1/256),1,1] 5314009514288286095091171328000000000000 5382530228347075503849368922532947689472 18684602901886604234313626025984000000000000 raw01335 affine01335
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01335_raw leaf01335_rectangular
    leaf01335_transform leaf01335_sign leaf01335_log
#print axioms leaf01335_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
