/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00066 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3117964708916128521408701530112000000000000 1490200256951945123911486143599587885056 8816438069347048680018935808000000000000))
theorem leaf00066_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3117964708916128521408701530112000000000000 1490200256951945123911486143599587885056 8816438069347048680018935808000000000000 raw00066=true := by decide +kernel
#print axioms leaf00066_raw
theorem leaf00066_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00066=true := by decide +kernel
#print axioms leaf00066_rectangular
def affine00066 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00066 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/3200),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00066_transform : affine00066=(NestedInteger.clearedAll 3 raw00066 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/3200),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00066_transform
theorem leaf00066_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00066=true := by decide +kernel
#print axioms leaf00066_sign
theorem leaf00066_log : RationalLog.accepts (1755939/4294967296) (-1047192975/268435456) 12 8=true := by decide +kernel
#print axioms leaf00066_log
def leaf00066 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (169025205557/1000000000000) (1755939/4294967296) (-1047192975/268435456) 12 8 ![52,0,4] ![(23/3200),0,0] ![(1/3200),1,(1/4)] affine00066
theorem leaf00066_checked : FastNestedCellData.accepts 1 0 4 leaf00066=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (169025205557/1000000000000) (1755939/4294967296) (-1047192975/268435456) 12 8 ![52,0,4] ![(23/3200),0,0] ![(1/3200),1,(1/4)] 3117964708916128521408701530112000000000000 1490200256951945123911486143599587885056 8816438069347048680018935808000000000000 raw00066 affine00066
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00066_raw leaf00066_rectangular
    leaf00066_transform leaf00066_sign leaf00066_log
#print axioms leaf00066_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
