/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00049 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1907246319899480384867192012800000000000 1727042556660014518106915520291689988096 41759566809377010042517900492800000000000))
theorem leaf00049_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1907246319899480384867192012800000000000 1727042556660014518106915520291689988096 41759566809377010042517900492800000000000 raw00049=true := by decide +kernel
#print axioms leaf00049_raw
theorem leaf00049_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00049=true := by decide +kernel
#print axioms leaf00049_rectangular
def affine00049 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00049 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00049_transform : affine00049=(NestedInteger.clearedAll 3 raw00049 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00049_transform
theorem leaf00049_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00049=true := by decide +kernel
#print axioms leaf00049_sign
theorem leaf00049_log : RationalLog.accepts (1867353573/2147483648) (-300163561/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00049_log
def leaf00049 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (4135681207/100000000000) (1867353573/2147483648) (-300163561/4294967296) 1 8 ![52,0,4] ![(17/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00049
theorem leaf00049_checked : FastNestedCellData.accepts 1 0 4 leaf00049=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (4135681207/100000000000) (1867353573/2147483648) (-300163561/4294967296) 1 8 ![52,0,4] ![(17/3200),0,(1/4)] ![(1/3200),1,(1/4)] 1907246319899480384867192012800000000000 1727042556660014518106915520291689988096 41759566809377010042517900492800000000000 raw00049 affine00049
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00049_raw leaf00049_rectangular
    leaf00049_transform leaf00049_sign leaf00049_log
#print axioms leaf00049_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
