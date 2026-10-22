/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00393 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3997210712828017859071311872000000000000 5232060664731620874111930329998313914368 23579548993447294106962231296000000000000))
theorem leaf00393_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3997210712828017859071311872000000000000 5232060664731620874111930329998313914368 23579548993447294106962231296000000000000 raw00393=true := by decide +kernel
#print axioms leaf00393_raw
theorem leaf00393_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00393=true := by decide +kernel
#print axioms leaf00393_rectangular
def affine00393 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00393 (IntegerComputedClassCell.leftNumerator ![(5/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/8),0,0] ![(1/16),1,(1/2)]))
theorem leaf00393_transform : affine00393=(NestedInteger.clearedAll 3 raw00393 (IntegerComputedClassCell.leftNumerator ![(5/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/8),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf00393_transform
theorem leaf00393_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00393=true := by decide +kernel
#print axioms leaf00393_sign
theorem leaf00393_log : RationalLog.accepts (143778379/134217728) (147767839/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00393_log
def leaf00393 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (221889768383/1000000000000) (143778379/134217728) (147767839/4294967296) 0 8 ![52,0,4] ![(5/8),0,0] ![(1/16),1,(1/2)] affine00393
theorem leaf00393_checked : FastNestedCellData.accepts 1 0 4 leaf00393=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (221889768383/1000000000000) (143778379/134217728) (147767839/4294967296) 0 8 ![52,0,4] ![(5/8),0,0] ![(1/16),1,(1/2)] 3997210712828017859071311872000000000000 5232060664731620874111930329998313914368 23579548993447294106962231296000000000000 raw00393 affine00393
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00393_raw leaf00393_rectangular
    leaf00393_transform leaf00393_sign leaf00393_log
#print axioms leaf00393_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
