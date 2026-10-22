/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00056 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 408354521117618706772343652352000000000000 386871784370723397013822895383174430326784 17476296763151403762518035791872000000000000))
theorem leaf00056_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 408354521117618706772343652352000000000000 386871784370723397013822895383174430326784 17476296763151403762518035791872000000000000 raw00056=true := by decide +kernel
#print axioms leaf00056_raw
theorem leaf00056_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00056=true := by decide +kernel
#print axioms leaf00056_rectangular
def affine00056 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00056 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00056_transform : affine00056=(NestedInteger.clearedAll 3 raw00056 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00056_transform
theorem leaf00056_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00056=true := by decide +kernel
#print axioms leaf00056_sign
theorem leaf00056_log : RationalLog.accepts (3980892631/4294967296) (-163075365/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00056_log
def leaf00056 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (22136942947/1000000000000) (3980892631/4294967296) (-163075365/4294967296) 1 8 ![52,0,4] ![(19/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00056
theorem leaf00056_checked : FastNestedCellData.accepts 1 0 4 leaf00056=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (22136942947/1000000000000) (3980892631/4294967296) (-163075365/4294967296) 1 8 ![52,0,4] ![(19/3200),0,(1/2)] ![(1/3200),1,(1/2)] 408354521117618706772343652352000000000000 386871784370723397013822895383174430326784 17476296763151403762518035791872000000000000 raw00056 affine00056
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00056_raw leaf00056_rectangular
    leaf00056_transform leaf00056_sign leaf00056_log
#print axioms leaf00056_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
