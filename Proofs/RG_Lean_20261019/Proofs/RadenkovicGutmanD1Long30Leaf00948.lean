/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00948 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 126958654393021277176124669952000000000000 68307095920098361356575398399891155714048 155075524744717477128234336256000000000000))
theorem leaf00948_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 126958654393021277176124669952000000000000 68307095920098361356575398399891155714048 155075524744717477128234336256000000000000 raw00948=true := by decide +kernel
#print axioms leaf00948_raw
theorem leaf00948_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00948=true := by decide +kernel
#print axioms leaf00948_rectangular
def affine00948 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00948 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00948_transform : affine00948=(NestedInteger.clearedAll 3 raw00948 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00948_transform
theorem leaf00948_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00948=true := by decide +kernel
#print axioms leaf00948_sign
theorem leaf00948_log : RationalLog.accepts (802097669/2147483648) (-528722119/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00948_log
def leaf00948 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (110119079127/250000000000) (802097669/2147483648) (-528722119/1073741824) 2 8 ![60,0,4] ![(3/32),0,(1/4)] ![(1/320),1,(1/4)] affine00948
theorem leaf00948_checked : FastNestedCellData.accepts 1 2 4 leaf00948=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (110119079127/250000000000) (802097669/2147483648) (-528722119/1073741824) 2 8 ![60,0,4] ![(3/32),0,(1/4)] ![(1/320),1,(1/4)] 126958654393021277176124669952000000000000 68307095920098361356575398399891155714048 155075524744717477128234336256000000000000 raw00948 affine00948
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00948_raw leaf00948_rectangular
    leaf00948_transform leaf00948_sign leaf00948_log
#print axioms leaf00948_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
