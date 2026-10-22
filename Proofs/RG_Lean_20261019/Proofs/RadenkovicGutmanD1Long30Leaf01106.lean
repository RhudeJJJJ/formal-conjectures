/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01106 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 57923538340553024922607157248000000000000 68326957946126281366435491510201691930624 339998303873059634607000911872000000000000))
theorem leaf01106_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 57923538340553024922607157248000000000000 68326957946126281366435491510201691930624 339998303873059634607000911872000000000000 raw01106=true := by decide +kernel
#print axioms leaf01106_raw
theorem leaf01106_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01106=true := by decide +kernel
#print axioms leaf01106_rectangular
def affine01106 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01106 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf01106_transform : affine01106=(NestedInteger.clearedAll 3 raw01106 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf01106_transform
theorem leaf01106_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01106=true := by decide +kernel
#print axioms leaf01106_sign
theorem leaf01106_log : RationalLog.accepts (1054647611/1073741824) (-38532093/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01106_log
def leaf01106 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (100481321771/500000000000) (1054647611/1073741824) (-38532093/4294967296) 1 8 ![60,0,4] ![(9/16),0,(1/2)] ![(1/32),1,(1/4)] affine01106
theorem leaf01106_checked : FastNestedCellData.accepts 1 2 4 leaf01106=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (100481321771/500000000000) (1054647611/1073741824) (-38532093/4294967296) 1 8 ![60,0,4] ![(9/16),0,(1/2)] ![(1/32),1,(1/4)] 57923538340553024922607157248000000000000 68326957946126281366435491510201691930624 339998303873059634607000911872000000000000 raw01106 affine01106
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01106_raw leaf01106_rectangular
    leaf01106_transform leaf01106_sign leaf01106_log
#print axioms leaf01106_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
