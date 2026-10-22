/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01240 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 6647655013434647514454163456000000000000 7224598715942025304172575983102578393088 1252982473508507376014535426048000000000000))
theorem leaf01240_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 6647655013434647514454163456000000000000 7224598715942025304172575983102578393088 1252982473508507376014535426048000000000000 raw01240=true := by decide +kernel
#print axioms leaf01240_raw
theorem leaf01240_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01240=true := by decide +kernel
#print axioms leaf01240_rectangular
def affine01240 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01240 (IntegerComputedClassCell.leftNumerator ![(15/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf01240_transform : affine01240=(NestedInteger.clearedAll 3 raw01240 (IntegerComputedClassCell.leftNumerator ![(15/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf01240_transform
theorem leaf01240_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01240=true := by decide +kernel
#print axioms leaf01240_sign
theorem leaf01240_log : RationalLog.accepts (2320482009/2147483648) (83191547/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01240_log
def leaf01240 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2882960803/500000000000) (2320482009/2147483648) (83191547/2147483648) 0 8 ![60,0,4] ![(15/64),0,0] ![(1/64),1,(1/2)] affine01240
theorem leaf01240_checked : FastNestedCellData.accepts 1 2 4 leaf01240=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2882960803/500000000000) (2320482009/2147483648) (83191547/2147483648) 0 8 ![60,0,4] ![(15/64),0,0] ![(1/64),1,(1/2)] 6647655013434647514454163456000000000000 7224598715942025304172575983102578393088 1252982473508507376014535426048000000000000 raw01240 affine01240
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01240_raw leaf01240_rectangular
    leaf01240_transform leaf01240_sign leaf01240_log
#print axioms leaf01240_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
