/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01275 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 4979854552977466765135052800000000000 5235253411051542411696131110940442624 2164376265359436874009018368000000000000))
theorem leaf01275_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 4979854552977466765135052800000000000 5235253411051542411696131110940442624 2164376265359436874009018368000000000000 raw01275=true := by decide +kernel
#print axioms leaf01275_raw
theorem leaf01275_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01275=true := by decide +kernel
#print axioms leaf01275_rectangular
def affine01275 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01275 (IntegerComputedClassCell.leftNumerator ![(11/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/64),0,0] ![(1/128),1,(1/2)]))
theorem leaf01275_transform : affine01275=(NestedInteger.clearedAll 3 raw01275 (IntegerComputedClassCell.leftNumerator ![(11/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/64),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01275_transform
theorem leaf01275_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01275=true := by decide +kernel
#print axioms leaf01275_sign
theorem leaf01275_log : RationalLog.accepts (2252172755/2147483648) (102217341/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01275_log
def leaf01275 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (302353471/125000000000) (2252172755/2147483648) (102217341/4294967296) 0 8 ![60,0,4] ![(11/64),0,0] ![(1/128),1,(1/2)] affine01275
theorem leaf01275_checked : FastNestedCellData.accepts 1 2 4 leaf01275=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (302353471/125000000000) (2252172755/2147483648) (102217341/4294967296) 0 8 ![60,0,4] ![(11/64),0,0] ![(1/128),1,(1/2)] 4979854552977466765135052800000000000 5235253411051542411696131110940442624 2164376265359436874009018368000000000000 raw01275 affine01275
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01275_raw leaf01275_rectangular
    leaf01275_transform leaf01275_sign leaf01275_log
#print axioms leaf01275_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
