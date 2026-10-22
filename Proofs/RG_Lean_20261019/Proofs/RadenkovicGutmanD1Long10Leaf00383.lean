/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00383 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 5531062973718746987978825924608000000000000 6273278048540971714648733365650654270324736 20922118445317813096811459510272000000000000))
theorem leaf00383_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 5531062973718746987978825924608000000000000 6273278048540971714648733365650654270324736 20922118445317813096811459510272000000000000 raw00383=true := by decide +kernel
#print axioms leaf00383_raw
theorem leaf00383_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00383=true := by decide +kernel
#print axioms leaf00383_rectangular
def affine00383 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00383 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)]))
theorem leaf00383_transform : affine00383=(NestedInteger.clearedAll 3 raw00383 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)])) := by decide +kernel
#print axioms leaf00383_transform
theorem leaf00383_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00383=true := by decide +kernel
#print axioms leaf00383_sign
theorem leaf00383_log : RationalLog.accepts (3747624389/4294967296) (-73187217/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00383_log
def leaf00383 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (299839524613/1000000000000) (3747624389/4294967296) (-73187217/1073741824) 1 8 ![52,0,4] ![(17/40),0,(1/2)] ![(3/80),1,(1/2)] affine00383
theorem leaf00383_checked : FastNestedCellData.accepts 1 0 4 leaf00383=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (299839524613/1000000000000) (3747624389/4294967296) (-73187217/1073741824) 1 8 ![52,0,4] ![(17/40),0,(1/2)] ![(3/80),1,(1/2)] 5531062973718746987978825924608000000000000 6273278048540971714648733365650654270324736 20922118445317813096811459510272000000000000 raw00383 affine00383
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00383_raw leaf00383_rectangular
    leaf00383_transform leaf00383_sign leaf00383_log
#print axioms leaf00383_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
