/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00392 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 72462497596637480373520328294400000000000 90994781801749328970947043738013919084544 386074983063102025934974222336000000000000))
theorem leaf00392_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 72462497596637480373520328294400000000000 90994781801749328970947043738013919084544 386074983063102025934974222336000000000000 raw00392=true := by decide +kernel
#print axioms leaf00392_raw
theorem leaf00392_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00392=true := by decide +kernel
#print axioms leaf00392_rectangular
def affine00392 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00392 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)]))
theorem leaf00392_transform : affine00392=(NestedInteger.clearedAll 3 raw00392 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(3/4)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00392_transform
theorem leaf00392_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00392=true := by decide +kernel
#print axioms leaf00392_sign
theorem leaf00392_log : RationalLog.accepts (4364684115/4294967296) (34578519/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00392_log
def leaf00392 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (117845995977/500000000000) (4364684115/4294967296) (34578519/4294967296) 0 8 ![52,0,4] ![(9/16),0,(3/4)] ![(1/16),1,(1/4)] affine00392
theorem leaf00392_checked : FastNestedCellData.accepts 1 0 4 leaf00392=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (117845995977/500000000000) (4364684115/4294967296) (34578519/4294967296) 0 8 ![52,0,4] ![(9/16),0,(3/4)] ![(1/16),1,(1/4)] 72462497596637480373520328294400000000000 90994781801749328970947043738013919084544 386074983063102025934974222336000000000000 raw00392 affine00392
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00392_raw leaf00392_rectangular
    leaf00392_transform leaf00392_sign leaf00392_log
#print axioms leaf00392_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
