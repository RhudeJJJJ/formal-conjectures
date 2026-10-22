/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00007 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 20443142691679429303101030400000000000 19623114712873732724359826944083099648 1152786254593703456247119872000000000000))
theorem leaf00007_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 20443142691679429303101030400000000000 19623114712873732724359826944083099648 1152786254593703456247119872000000000000 raw00007=true := by decide +kernel
#print axioms leaf00007_raw
theorem leaf00007_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00007=true := by decide +kernel
#print axioms leaf00007_rectangular
def affine00007 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00007 (IntegerComputedClassCell.leftNumerator ![(17/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/16000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00007_transform : affine00007=(NestedInteger.clearedAll 3 raw00007 (IntegerComputedClassCell.leftNumerator ![(17/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/16000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00007_transform
theorem leaf00007_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00007=true := by decide +kernel
#print axioms leaf00007_sign
theorem leaf00007_log : RationalLog.accepts (1013420445/1073741824) (-62082043/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00007_log
def leaf00007 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2127791973/125000000000) (1013420445/1073741824) (-62082043/2147483648) 1 8 ![60,0,4] ![(17/16000),0,(1/8)] ![(1/16000),1,(1/8)] affine00007
theorem leaf00007_checked : FastNestedCellData.accepts 1 2 4 leaf00007=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2127791973/125000000000) (1013420445/1073741824) (-62082043/2147483648) 1 8 ![60,0,4] ![(17/16000),0,(1/8)] ![(1/16000),1,(1/8)] 20443142691679429303101030400000000000 19623114712873732724359826944083099648 1152786254593703456247119872000000000000 raw00007 affine00007
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00007_raw leaf00007_rectangular
    leaf00007_transform leaf00007_sign leaf00007_log
#print axioms leaf00007_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
