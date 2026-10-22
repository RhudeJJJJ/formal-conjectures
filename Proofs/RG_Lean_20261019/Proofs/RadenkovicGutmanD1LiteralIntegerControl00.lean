/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLiteralIntegerCell
import Proofs.RadenkovicGutmanD1Norm00Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneLiteralIntegerControl00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00000 : NestedInteger.Poly 3 := rg_integer_data%
  (PackedIntegerSemanticAffine.raw (NormProgramPack.polynomial DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912)) (IntegerComputedClassCell.baseScale (629387643537/1000000000000) (12727/536870912)) ![88,4,4])
def affine00000 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00000 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.denominator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]))
theorem leaf00000_raw : LiteralIntegerCell.rawCheck (NormProgramPack.polynomial DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912)) (IntegerComputedClassCell.baseScale (629387643537/1000000000000) (12727/536870912)) raw00000=true := by decide +kernel
#print axioms leaf00000_raw
theorem leaf00000_rectangular : NestedInteger.rectangular 3 ![88,4,4] raw00000=true := by decide +kernel
#print axioms leaf00000_rectangular
theorem leaf00000_transform : affine00000=(NestedInteger.clearedAll 3 raw00000 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.denominator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)])) := by decide +kernel
#print axioms leaf00000_transform
theorem leaf00000_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] affine00000=true := by decide +kernel
#print axioms leaf00000_sign
theorem leaf00000_log : RationalLog.accepts (12727/536870912) (-22870244509/4294967296) 16 8=true := by decide +kernel
#print axioms leaf00000_log
def leaf00000 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912) (-22870244509/4294967296) 16 8 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)] affine00000
theorem leaf00000_checked : FastNestedCellData.accepts 1 4 4 leaf00000=true :=
  LiteralIntegerCell.accepts_make DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912) (-22870244509/4294967296) 16 8 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)] raw00000 affine00000
    (by decide +kernel) (by decide +kernel) leaf00000_raw leaf00000_rectangular
    leaf00000_transform leaf00000_sign leaf00000_log
#print axioms leaf00000_checked
def raw01753 : NestedInteger.Poly 3 := rg_integer_data%
  (PackedIntegerSemanticAffine.raw (NormProgramPack.polynomial DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912)) (IntegerComputedClassCell.baseScale (1571/1000000000000) (536871935/536870912)) ![88,4,4])
def affine01753 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01753 (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1]))
theorem leaf01753_raw : LiteralIntegerCell.rawCheck (NormProgramPack.polynomial DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912)) (IntegerComputedClassCell.baseScale (1571/1000000000000) (536871935/536870912)) raw01753=true := by decide +kernel
#print axioms leaf01753_raw
theorem leaf01753_rectangular : NestedInteger.rectangular 3 ![88,4,4] raw01753=true := by decide +kernel
#print axioms leaf01753_rectangular
theorem leaf01753_transform : affine01753=(NestedInteger.clearedAll 3 raw01753 (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1])) := by decide +kernel
#print axioms leaf01753_transform
theorem leaf01753_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] affine01753=true := by decide +kernel
#print axioms leaf01753_sign
theorem leaf01753_log : RationalLog.accepts (536871935/536870912) (4091/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01753_log
def leaf01753 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] affine01753
theorem leaf01753_checked : FastNestedCellData.accepts 1 4 4 leaf01753=true :=
  LiteralIntegerCell.accepts_make DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] raw01753 affine01753
    (by decide +kernel) (by decide +kernel) leaf01753_raw leaf01753_rectangular
    leaf01753_transform leaf01753_sign leaf01753_log
#print axioms leaf01753_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLiteralIntegerControl00
