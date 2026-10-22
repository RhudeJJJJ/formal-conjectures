/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01004 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6185256812026595342668512886784000000000000 4350030071399277753534364840737207912235008 12973413049562788665931220385792000000000000))
theorem leaf01004_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6185256812026595342668512886784000000000000 4350030071399277753534364840737207912235008 12973413049562788665931220385792000000000000 raw01004=true := by decide +kernel
#print axioms leaf01004_raw
theorem leaf01004_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01004=true := by decide +kernel
#print axioms leaf01004_rectangular
def affine01004 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01004 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf01004_transform : affine01004=(NestedInteger.clearedAll 3 raw01004 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01004_transform
theorem leaf01004_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01004=true := by decide +kernel
#print axioms leaf01004_sign
theorem leaf01004_log : RationalLog.accepts (2262113623/4294967296) (-43026469/134217728) 1 8=true := by decide +kernel
#print axioms leaf01004_log
def leaf01004 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (335303443649/1000000000000) (2262113623/4294967296) (-43026469/134217728) 1 8 ![60,0,4] ![(3/20),0,(1/2)] ![(1/160),1,(1/2)] affine01004
theorem leaf01004_checked : FastNestedCellData.accepts 1 2 4 leaf01004=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (335303443649/1000000000000) (2262113623/4294967296) (-43026469/134217728) 1 8 ![60,0,4] ![(3/20),0,(1/2)] ![(1/160),1,(1/2)] 6185256812026595342668512886784000000000000 4350030071399277753534364840737207912235008 12973413049562788665931220385792000000000000 raw01004 affine01004
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01004_raw leaf01004_rectangular
    leaf01004_transform leaf01004_sign leaf01004_log
#print axioms leaf01004_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
