/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01167 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1064181171427624960231718518784000000000000 1350002689647906673224195163064010975215616 23401235413088816160142717353984000000000000))
theorem leaf01167_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1064181171427624960231718518784000000000000 1350002689647906673224195163064010975215616 23401235413088816160142717353984000000000000 raw01167=true := by decide +kernel
#print axioms leaf01167_raw
theorem leaf01167_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01167=true := by decide +kernel
#print axioms leaf01167_rectangular
def affine01167 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01167 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(3/4)] ![(1/8),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(3/4)] ![(1/8),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/8),0,(3/4)] ![(1/8),1,(1/8)]))
theorem leaf01167_transform : affine01167=(NestedInteger.clearedAll 3 raw01167 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(3/4)] ![(1/8),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(3/4)] ![(1/8),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/8),0,(3/4)] ![(1/8),1,(1/8)])) := by decide +kernel
#print axioms leaf01167_transform
theorem leaf01167_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01167=true := by decide +kernel
#print axioms leaf01167_sign
theorem leaf01167_log : RationalLog.accepts (5151346721/4294967296) (12201347/134217728) 0 8=true := by decide +kernel
#print axioms leaf01167_log
def leaf01167 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (57689376899/1000000000000) (5151346721/4294967296) (12201347/134217728) 0 8 ![60,0,4] ![(5/8),0,(3/4)] ![(1/8),1,(1/8)] affine01167
theorem leaf01167_checked : FastNestedCellData.accepts 1 2 4 leaf01167=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (57689376899/1000000000000) (5151346721/4294967296) (12201347/134217728) 0 8 ![60,0,4] ![(5/8),0,(3/4)] ![(1/8),1,(1/8)] 1064181171427624960231718518784000000000000 1350002689647906673224195163064010975215616 23401235413088816160142717353984000000000000 raw01167 affine01167
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01167_raw leaf01167_rectangular
    leaf01167_transform leaf01167_sign leaf01167_log
#print axioms leaf01167_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
