/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00065 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1839931026587821047386472448000000000000 1729805285970177918321147489001536487424 67744717198588698675661242368000000000000))
theorem leaf00065_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1839931026587821047386472448000000000000 1729805285970177918321147489001536487424 67744717198588698675661242368000000000000 raw00065=true := by decide +kernel
#print axioms leaf00065_raw
theorem leaf00065_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00065=true := by decide +kernel
#print axioms leaf00065_rectangular
def affine00065 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00065 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00065_transform : affine00065=(NestedInteger.clearedAll 3 raw00065 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00065_transform
theorem leaf00065_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00065=true := by decide +kernel
#print axioms leaf00065_sign
theorem leaf00065_log : RationalLog.accepts (3937362511/4294967296) (-186686921/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00065_log
def leaf00065 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1595885773/62500000000) (3937362511/4294967296) (-186686921/4294967296) 1 8 ![52,0,4] ![(11/1600),0,(1/2)] ![(1/3200),1,(1/2)] affine00065
theorem leaf00065_checked : FastNestedCellData.accepts 1 0 4 leaf00065=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1595885773/62500000000) (3937362511/4294967296) (-186686921/4294967296) 1 8 ![52,0,4] ![(11/1600),0,(1/2)] ![(1/3200),1,(1/2)] 1839931026587821047386472448000000000000 1729805285970177918321147489001536487424 67744717198588698675661242368000000000000 raw00065 affine00065
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00065_raw leaf00065_rectangular
    leaf00065_transform leaf00065_sign leaf00065_log
#print axioms leaf00065_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
