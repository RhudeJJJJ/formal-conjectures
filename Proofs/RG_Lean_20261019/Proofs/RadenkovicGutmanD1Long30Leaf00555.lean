/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00555 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4958458060949767794385945100288000000000000 50778318146647003039151803791750444613632 62969484184442856247664836608000000000000))
theorem leaf00555_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4958458060949767794385945100288000000000000 50778318146647003039151803791750444613632 62969484184442856247664836608000000000000 raw00555=true := by decide +kernel
#print axioms leaf00555_raw
theorem leaf00555_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00555=true := by decide +kernel
#print axioms leaf00555_rectangular
def affine00555 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00555 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/1600),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00555_transform : affine00555=(NestedInteger.clearedAll 3 raw00555 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/1600),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00555_transform
theorem leaf00555_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00555=true := by decide +kernel
#print axioms leaf00555_sign
theorem leaf00555_log : RationalLog.accepts (24348861/4294967296) (-5554159665/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00555_log
def leaf00555 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (806395650279/1000000000000) (24348861/4294967296) (-5554159665/2147483648) 8 8 ![60,0,4] ![(27/1600),0,0] ![(1/3200),1,(1/16)] affine00555
theorem leaf00555_checked : FastNestedCellData.accepts 1 2 4 leaf00555=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (806395650279/1000000000000) (24348861/4294967296) (-5554159665/2147483648) 8 8 ![60,0,4] ![(27/1600),0,0] ![(1/3200),1,(1/16)] 4958458060949767794385945100288000000000000 50778318146647003039151803791750444613632 62969484184442856247664836608000000000000 raw00555 affine00555
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00555_raw leaf00555_rectangular
    leaf00555_transform leaf00555_sign leaf00555_log
#print axioms leaf00555_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
