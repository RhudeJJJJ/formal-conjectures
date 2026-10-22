/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00976 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12396765457910662996563284983808000000000000 5567964450080125272852299251649612378800128 8285291479528546271126152544256000000000000))
theorem leaf00976_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12396765457910662996563284983808000000000000 5567964450080125272852299251649612378800128 8285291479528546271126152544256000000000000 raw00976=true := by decide +kernel
#print axioms leaf00976_raw
theorem leaf00976_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00976=true := by decide +kernel
#print axioms leaf00976_rectangular
def affine00976 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00976 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/16)] ![(1/160),1,(1/16)]))
theorem leaf00976_transform : affine00976=(NestedInteger.clearedAll 3 raw00976 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/16)] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00976_transform
theorem leaf00976_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00976=true := by decide +kernel
#print axioms leaf00976_sign
theorem leaf00976_log : RationalLog.accepts (1153729147/4294967296) (-2822748159/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00976_log
def leaf00976 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (672030002063/1000000000000) (1153729147/4294967296) (-2822748159/4294967296) 2 8 ![60,0,4] ![(19/160),0,(1/16)] ![(1/160),1,(1/16)] affine00976
theorem leaf00976_checked : FastNestedCellData.accepts 1 2 4 leaf00976=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (672030002063/1000000000000) (1153729147/4294967296) (-2822748159/4294967296) 2 8 ![60,0,4] ![(19/160),0,(1/16)] ![(1/160),1,(1/16)] 12396765457910662996563284983808000000000000 5567964450080125272852299251649612378800128 8285291479528546271126152544256000000000000 raw00976 affine00976
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00976_raw leaf00976_rectangular
    leaf00976_transform leaf00976_sign leaf00976_log
#print axioms leaf00976_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
