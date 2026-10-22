/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00291 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 25972119996629577477974938091520000000000 3329615333177128188750434065376297877504 4729730335682126714226763366400000000000))
theorem leaf00291_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 25972119996629577477974938091520000000000 3329615333177128188750434065376297877504 4729730335682126714226763366400000000000 raw00291=true := by decide +kernel
#print axioms leaf00291_raw
theorem leaf00291_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00291=true := by decide +kernel
#print axioms leaf00291_rectangular
def affine00291 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00291 (IntegerComputedClassCell.leftNumerator ![(23/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/320),0,0] ![(1/320),1,(1/4)]))
theorem leaf00291_transform : affine00291=(NestedInteger.clearedAll 3 raw00291 (IntegerComputedClassCell.leftNumerator ![(23/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/320),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00291_transform
theorem leaf00291_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00291=true := by decide +kernel
#print axioms leaf00291_sign
theorem leaf00291_log : RationalLog.accepts (323134345/4294967296) (-347238861/268435456) 4 8=true := by decide +kernel
#print axioms leaf00291_log
def leaf00291 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (70397572311/100000000000) (323134345/4294967296) (-347238861/268435456) 4 8 ![52,0,4] ![(23/320),0,0] ![(1/320),1,(1/4)] affine00291
theorem leaf00291_checked : FastNestedCellData.accepts 1 0 4 leaf00291=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (70397572311/100000000000) (323134345/4294967296) (-347238861/268435456) 4 8 ![52,0,4] ![(23/320),0,0] ![(1/320),1,(1/4)] 25972119996629577477974938091520000000000 3329615333177128188750434065376297877504 4729730335682126714226763366400000000000 raw00291 affine00291
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00291_raw leaf00291_rectangular
    leaf00291_transform leaf00291_sign leaf00291_log
#print axioms leaf00291_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
