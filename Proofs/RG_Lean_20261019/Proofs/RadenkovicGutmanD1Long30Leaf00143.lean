/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00143 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 274109705682196809403565342720000000000 258983051211381146791459945836856737792 10725394790347594724300921241600000000000))
theorem leaf00143_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 274109705682196809403565342720000000000 258983051211381146791459945836856737792 10725394790347594724300921241600000000000 raw00143=true := by decide +kernel
#print axioms leaf00143_raw
theorem leaf00143_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00143=true := by decide +kernel
#print axioms leaf00143_rectangular
def affine00143 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00143 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00143_transform : affine00143=(NestedInteger.clearedAll 3 raw00143 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00143_transform
theorem leaf00143_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00143=true := by decide +kernel
#print axioms leaf00143_sign
theorem leaf00143_log : RationalLog.accepts (3962275005/4294967296) (-10821385/268435456) 1 8=true := by decide +kernel
#print axioms leaf00143_log
def leaf00143 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4829342999/200000000000) (3962275005/4294967296) (-10821385/268435456) 1 8 ![60,0,4] ![(1/320),0,(1/4)] ![(3/32000),1,(1/4)] affine00143
theorem leaf00143_checked : FastNestedCellData.accepts 1 2 4 leaf00143=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4829342999/200000000000) (3962275005/4294967296) (-10821385/268435456) 1 8 ![60,0,4] ![(1/320),0,(1/4)] ![(3/32000),1,(1/4)] 274109705682196809403565342720000000000 258983051211381146791459945836856737792 10725394790347594724300921241600000000000 raw00143 affine00143
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00143_raw leaf00143_rectangular
    leaf00143_transform leaf00143_sign leaf00143_log
#print axioms leaf00143_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
