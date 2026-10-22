/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00399 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8234809208975614942631690240000000000 11080808867753919328763168924601679872 64640755014635354720514867200000000000))
theorem leaf00399_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8234809208975614942631690240000000000 11080808867753919328763168924601679872 64640755014635354720514867200000000000 raw00399=true := by decide +kernel
#print axioms leaf00399_raw
theorem leaf00399_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00399=true := by decide +kernel
#print axioms leaf00399_rectangular
def affine00399 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00399 (IntegerComputedClassCell.leftNumerator ![(3/4),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/4),0,0] ![(1/8),1,(1/2)]))
theorem leaf00399_transform : affine00399=(NestedInteger.clearedAll 3 raw00399 (IntegerComputedClassCell.leftNumerator ![(3/4),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/4),0,0] ![(1/8),1,(1/2)])) := by decide +kernel
#print axioms leaf00399_transform
theorem leaf00399_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00399=true := by decide +kernel
#print axioms leaf00399_sign
theorem leaf00399_log : RationalLog.accepts (616700985/536870912) (148849179/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00399_log
def leaf00399 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (8571070113/50000000000) (616700985/536870912) (148849179/2147483648) 0 8 ![52,0,4] ![(3/4),0,0] ![(1/8),1,(1/2)] affine00399
theorem leaf00399_checked : FastNestedCellData.accepts 1 0 4 leaf00399=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (8571070113/50000000000) (616700985/536870912) (148849179/2147483648) 0 8 ![52,0,4] ![(3/4),0,0] ![(1/8),1,(1/2)] 8234809208975614942631690240000000000 11080808867753919328763168924601679872 64640755014635354720514867200000000000 raw00399 affine00399
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00399_raw leaf00399_rectangular
    leaf00399_transform leaf00399_sign leaf00399_log
#print axioms leaf00399_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
