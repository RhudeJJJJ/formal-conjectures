/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01364 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 7191347884985208012800000000000 7191378738054841548280317345792 2882316127476890400112351641600000000000))
theorem leaf01364_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 7191347884985208012800000000000 7191378738054841548280317345792 2882316127476890400112351641600000000000 raw01364=true := by decide +kernel
#print axioms leaf01364_raw
theorem leaf01364_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01364=true := by decide +kernel
#print axioms leaf01364_rectangular
def affine01364 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01364 (IntegerComputedClassCell.leftNumerator ![(3/2048),0,0] ![(1/2048),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/2048),0,0] ![(1/2048),1,1]) (IntegerComputedClassCell.denominator ![(3/2048),0,0] ![(1/2048),1,1]))
theorem leaf01364_transform : affine01364=(NestedInteger.clearedAll 3 raw01364 (IntegerComputedClassCell.leftNumerator ![(3/2048),0,0] ![(1/2048),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/2048),0,0] ![(1/2048),1,1]) (IntegerComputedClassCell.denominator ![(3/2048),0,0] ![(1/2048),1,1])) := by decide +kernel
#print axioms leaf01364_transform
theorem leaf01364_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01364=true := by decide +kernel
#print axioms leaf01364_sign
theorem leaf01364_log : RationalLog.accepts (268436607/268435456) (9207/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01364_log
def leaf01364 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (499/200000000000) (268436607/268435456) (9207/4294967296) 0 8 ![60,0,4] ![(3/2048),0,0] ![(1/2048),1,1] affine01364
theorem leaf01364_checked : FastNestedCellData.accepts 1 2 4 leaf01364=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (499/200000000000) (268436607/268435456) (9207/4294967296) 0 8 ![60,0,4] ![(3/2048),0,0] ![(1/2048),1,1] 7191347884985208012800000000000 7191378738054841548280317345792 2882316127476890400112351641600000000000 raw01364 affine01364
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01364_raw leaf01364_rectangular
    leaf01364_transform leaf01364_sign leaf01364_log
#print axioms leaf01364_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
