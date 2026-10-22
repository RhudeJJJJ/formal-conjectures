/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00324 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3221556286340773110512613326848000000000000 837210426832102024740846685141297409294336 1198474053138062359349090582528000000000000))
theorem leaf00324_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3221556286340773110512613326848000000000000 837210426832102024740846685141297409294336 1198474053138062359349090582528000000000000 raw00324=true := by decide +kernel
#print axioms leaf00324_raw
theorem leaf00324_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00324=true := by decide +kernel
#print axioms leaf00324_rectangular
def affine00324 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00324 (IntegerComputedClassCell.leftNumerator ![(17/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/160),0,0] ![(1/160),1,(1/4)]))
theorem leaf00324_transform : affine00324=(NestedInteger.clearedAll 3 raw00324 (IntegerComputedClassCell.leftNumerator ![(17/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/160),0,0] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00324_transform
theorem leaf00324_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00324=true := by decide +kernel
#print axioms leaf00324_sign
theorem leaf00324_log : RationalLog.accepts (328561703/2147483648) (-4031529971/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00324_log
def leaf00324 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (698563664887/1000000000000) (328561703/2147483648) (-4031529971/4294967296) 3 8 ![52,0,4] ![(17/160),0,0] ![(1/160),1,(1/4)] affine00324
theorem leaf00324_checked : FastNestedCellData.accepts 1 0 4 leaf00324=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (698563664887/1000000000000) (328561703/2147483648) (-4031529971/4294967296) 3 8 ![52,0,4] ![(17/160),0,0] ![(1/160),1,(1/4)] 3221556286340773110512613326848000000000000 837210426832102024740846685141297409294336 1198474053138062359349090582528000000000000 raw00324 affine00324
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00324_raw leaf00324_rectangular
    leaf00324_transform leaf00324_sign leaf00324_log
#print axioms leaf00324_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
