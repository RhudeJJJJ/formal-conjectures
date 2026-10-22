/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00245 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 148096005919179003883645252403200000000000 107624434207362954712551004483416515149824 670281545264790116065194541056000000000000))
theorem leaf00245_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 148096005919179003883645252403200000000000 107624434207362954712551004483416515149824 670281545264790116065194541056000000000000 raw00245=true := by decide +kernel
#print axioms leaf00245_raw
theorem leaf00245_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00245=true := by decide +kernel
#print axioms leaf00245_rectangular
def affine00245 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00245 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00245_transform : affine00245=(NestedInteger.clearedAll 3 raw00245 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00245_transform
theorem leaf00245_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00245=true := by decide +kernel
#print axioms leaf00245_sign
theorem leaf00245_log : RationalLog.accepts (2689413305/4294967296) (-1005281957/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00245_log
def leaf00245 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (80283005677/500000000000) (2689413305/4294967296) (-1005281957/4294967296) 1 8 ![52,0,4] ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)] affine00245
theorem leaf00245_checked : FastNestedCellData.accepts 1 0 4 leaf00245=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (80283005677/500000000000) (2689413305/4294967296) (-1005281957/4294967296) 1 8 ![52,0,4] ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)] 148096005919179003883645252403200000000000 107624434207362954712551004483416515149824 670281545264790116065194541056000000000000 raw00245 affine00245
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00245_raw leaf00245_rectangular
    leaf00245_transform leaf00245_sign leaf00245_log
#print axioms leaf00245_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
