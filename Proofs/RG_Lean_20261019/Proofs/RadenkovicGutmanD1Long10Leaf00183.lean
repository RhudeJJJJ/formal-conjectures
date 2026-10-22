/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00183 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 18820453494408408525521436016640000000000 305355763920800894140747031512499617792 598584899152680664212019609600000000000))
theorem leaf00183_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 18820453494408408525521436016640000000000 305355763920800894140747031512499617792 598584899152680664212019609600000000000 raw00183=true := by decide +kernel
#print axioms leaf00183_raw
theorem leaf00183_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00183=true := by decide +kernel
#print axioms leaf00183_rectangular
def affine00183 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00183 (IntegerComputedClassCell.leftNumerator ![(11/400),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/400),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00183_transform : affine00183=(NestedInteger.clearedAll 3 raw00183 (IntegerComputedClassCell.leftNumerator ![(11/400),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/400),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00183_transform
theorem leaf00183_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00183=true := by decide +kernel
#print axioms leaf00183_sign
theorem leaf00183_log : RationalLog.accepts (23072345/2147483648) (-9735439823/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00183_log
def leaf00183 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (102025882829/200000000000) (23072345/2147483648) (-9735439823/4294967296) 7 8 ![52,0,4] ![(11/400),0,0] ![(3/3200),1,(1/4)] affine00183
theorem leaf00183_checked : FastNestedCellData.accepts 1 0 4 leaf00183=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (102025882829/200000000000) (23072345/2147483648) (-9735439823/4294967296) 7 8 ![52,0,4] ![(11/400),0,0] ![(3/3200),1,(1/4)] 18820453494408408525521436016640000000000 305355763920800894140747031512499617792 598584899152680664212019609600000000000 raw00183 affine00183
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00183_raw leaf00183_rectangular
    leaf00183_transform leaf00183_sign leaf00183_log
#print axioms leaf00183_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
