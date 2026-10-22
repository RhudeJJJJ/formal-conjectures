/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01110 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 878208617695701957259296768000000000000 1055148920964498243301681334299039629312 5410978885341165608463499264000000000000))
theorem leaf01110_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 878208617695701957259296768000000000000 1055148920964498243301681334299039629312 5410978885341165608463499264000000000000 raw01110=true := by decide +kernel
#print axioms leaf01110_raw
theorem leaf01110_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01110=true := by decide +kernel
#print axioms leaf01110_rectangular
def affine01110 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01110 (IntegerComputedClassCell.leftNumerator ![(19/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/32),0,0] ![(1/32),1,(1/2)]))
theorem leaf01110_transform : affine01110=(NestedInteger.clearedAll 3 raw01110 (IntegerComputedClassCell.leftNumerator ![(19/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/32),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf01110_transform
theorem leaf01110_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01110=true := by decide +kernel
#print axioms leaf01110_sign
theorem leaf01110_log : RationalLog.accepts (134945219/134217728) (1451053/536870912) 0 8=true := by decide +kernel
#print axioms leaf01110_log
def leaf01110 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (97500742779/500000000000) (134945219/134217728) (1451053/536870912) 0 8 ![60,0,4] ![(19/32),0,0] ![(1/32),1,(1/2)] affine01110
theorem leaf01110_checked : FastNestedCellData.accepts 1 2 4 leaf01110=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (97500742779/500000000000) (134945219/134217728) (1451053/536870912) 0 8 ![60,0,4] ![(19/32),0,0] ![(1/32),1,(1/2)] 878208617695701957259296768000000000000 1055148920964498243301681334299039629312 5410978885341165608463499264000000000000 raw01110 affine01110
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01110_raw leaf01110_rectangular
    leaf01110_transform leaf01110_sign leaf01110_log
#print axioms leaf01110_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
