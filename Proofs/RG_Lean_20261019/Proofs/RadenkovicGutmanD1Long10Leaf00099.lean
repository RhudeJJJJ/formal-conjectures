/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00099 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 174499402534197991200847298560000000000 245635357765899596495927985641095168 1014323982443871006097408000000000000))
theorem leaf00099_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 174499402534197991200847298560000000000 245635357765899596495927985641095168 1014323982443871006097408000000000000 raw00099=true := by decide +kernel
#print axioms leaf00099_raw
theorem leaf00099_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00099=true := by decide +kernel
#print axioms leaf00099_rectangular
def affine00099 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00099 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/1600),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00099_transform : affine00099=(NestedInteger.clearedAll 3 raw00099 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/1600),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00099_transform
theorem leaf00099_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00099=true := by decide +kernel
#print axioms leaf00099_sign
theorem leaf00099_log : RationalLog.accepts (4867175/4294967296) (-14565706625/4294967296) 10 8=true := by decide +kernel
#print axioms leaf00099_log
def leaf00099 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (7567705253/31250000000) (4867175/4294967296) (-14565706625/4294967296) 10 8 ![52,0,4] ![(17/1600),0,0] ![(1/3200),1,(1/4)] affine00099
theorem leaf00099_checked : FastNestedCellData.accepts 1 0 4 leaf00099=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (7567705253/31250000000) (4867175/4294967296) (-14565706625/4294967296) 10 8 ![52,0,4] ![(17/1600),0,0] ![(1/3200),1,(1/4)] 174499402534197991200847298560000000000 245635357765899596495927985641095168 1014323982443871006097408000000000000 raw00099 affine00099
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00099_raw leaf00099_rectangular
    leaf00099_transform leaf00099_sign leaf00099_log
#print axioms leaf00099_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
