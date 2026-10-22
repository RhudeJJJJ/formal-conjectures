/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01132 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 29913641606758185283001883033600000000000 37586547097064728855654357114413454983168 289729608997747380404906622976000000000000))
theorem leaf01132_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 29913641606758185283001883033600000000000 37586547097064728855654357114413454983168 289729608997747380404906622976000000000000 raw01132=true := by decide +kernel
#print axioms leaf01132_raw
theorem leaf01132_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01132=true := by decide +kernel
#print axioms leaf01132_rectangular
def affine01132 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01132 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01132_transform : affine01132=(NestedInteger.clearedAll 3 raw01132 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01132_transform
theorem leaf01132_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01132=true := by decide +kernel
#print axioms leaf01132_sign
theorem leaf01132_log : RationalLog.accepts (4776925235/4294967296) (228391633/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01132_log
def leaf01132 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (32432435217/250000000000) (4776925235/4294967296) (228391633/4294967296) 0 8 ![60,0,4] ![(13/16),0,(3/4)] ![(1/16),1,(1/8)] affine01132
theorem leaf01132_checked : FastNestedCellData.accepts 1 2 4 leaf01132=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (32432435217/250000000000) (4776925235/4294967296) (228391633/4294967296) 0 8 ![60,0,4] ![(13/16),0,(3/4)] ![(1/16),1,(1/8)] 29913641606758185283001883033600000000000 37586547097064728855654357114413454983168 289729608997747380404906622976000000000000 raw01132 affine01132
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01132_raw leaf01132_rectangular
    leaf01132_transform leaf01132_sign leaf01132_log
#print axioms leaf01132_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
