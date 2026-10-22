/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01023 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 509372264829956000922527072256000000000000 367329490407700318314802059404551303200768 831419568768021013093236604928000000000000))
theorem leaf01023_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 509372264829956000922527072256000000000000 367329490407700318314802059404551303200768 831419568768021013093236604928000000000000 raw01023=true := by decide +kernel
#print axioms leaf01023_raw
theorem leaf01023_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01023=true := by decide +kernel
#print axioms leaf01023_rectangular
def affine01023 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01023 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)]))
theorem leaf01023_transform : affine01023=(NestedInteger.clearedAll 3 raw01023 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf01023_transform
theorem leaf01023_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01023=true := by decide +kernel
#print axioms leaf01023_sign
theorem leaf01023_log : RationalLog.accepts (1074094099/2147483648) (-1487817837/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01023_log
def leaf01023 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (220905006453/500000000000) (1074094099/2147483648) (-1487817837/4294967296) 1 8 ![60,0,4] ![(3/16),0,(1/4)] ![(1/80),1,(1/4)] affine01023
theorem leaf01023_checked : FastNestedCellData.accepts 1 2 4 leaf01023=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (220905006453/500000000000) (1074094099/2147483648) (-1487817837/4294967296) 1 8 ![60,0,4] ![(3/16),0,(1/4)] ![(1/80),1,(1/4)] 509372264829956000922527072256000000000000 367329490407700318314802059404551303200768 831419568768021013093236604928000000000000 raw01023 affine01023
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01023_raw leaf01023_rectangular
    leaf01023_transform leaf01023_sign leaf01023_log
#print axioms leaf01023_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
