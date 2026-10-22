/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00513 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 491476853891034086790106447872000000000000 387825834405759786271295082035715854303232 3639095033579170605436632039424000000000000))
theorem leaf00513_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 491476853891034086790106447872000000000000 387825834405759786271295082035715854303232 3639095033579170605436632039424000000000000 raw00513=true := by decide +kernel
#print axioms leaf00513_raw
theorem leaf00513_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00513=true := by decide +kernel
#print axioms leaf00513_rectangular
def affine00513 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00513 (IntegerComputedClassCell.leftNumerator ![(9/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/640),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00513_transform : affine00513=(NestedInteger.clearedAll 3 raw00513 (IntegerComputedClassCell.leftNumerator ![(9/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/640),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00513_transform
theorem leaf00513_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00513=true := by decide +kernel
#print axioms leaf00513_sign
theorem leaf00513_log : RationalLog.accepts (1531383041/2147483648) (-363059493/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00513_log
def leaf00513 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (106572054543/1000000000000) (1531383041/2147483648) (-363059493/2147483648) 1 8 ![60,0,4] ![(9/640),0,(1/4)] ![(1/3200),1,(1/4)] affine00513
theorem leaf00513_checked : FastNestedCellData.accepts 1 2 4 leaf00513=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (106572054543/1000000000000) (1531383041/2147483648) (-363059493/2147483648) 1 8 ![60,0,4] ![(9/640),0,(1/4)] ![(1/3200),1,(1/4)] 491476853891034086790106447872000000000000 387825834405759786271295082035715854303232 3639095033579170605436632039424000000000000 raw00513 affine00513
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00513_raw leaf00513_rectangular
    leaf00513_transform leaf00513_sign leaf00513_log
#print axioms leaf00513_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
