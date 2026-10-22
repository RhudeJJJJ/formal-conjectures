/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00002 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 294771012545423462214139904000000000000 291278060541927523664326974739203489792 71203732203657200101415190528000000000000))
theorem leaf00002_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 294771012545423462214139904000000000000 291278060541927523664326974739203489792 71203732203657200101415190528000000000000 raw00002=true := by decide +kernel
#print axioms leaf00002_raw
theorem leaf00002_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00002=true := by decide +kernel
#print axioms leaf00002_rectangular
def affine00002 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00002 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/1000),0,(1/2)] ![(1/4000),1,(1/2)]))
theorem leaf00002_transform : affine00002=(NestedInteger.clearedAll 3 raw00002 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/1000),0,(1/2)] ![(1/4000),1,(1/2)])) := by decide +kernel
#print axioms leaf00002_transform
theorem leaf00002_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00002=true := by decide +kernel
#print axioms leaf00002_sign
theorem leaf00002_log : RationalLog.accepts (1056695593/1073741824) (-536969/67108864) 1 8=true := by decide +kernel
#print axioms leaf00002_log
def leaf00002 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1022692391/250000000000) (1056695593/1073741824) (-536969/67108864) 1 8 ![52,0,4] ![(1/1000),0,(1/2)] ![(1/4000),1,(1/2)] affine00002
theorem leaf00002_checked : FastNestedCellData.accepts 1 0 4 leaf00002=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1022692391/250000000000) (1056695593/1073741824) (-536969/67108864) 1 8 ![52,0,4] ![(1/1000),0,(1/2)] ![(1/4000),1,(1/2)] 294771012545423462214139904000000000000 291278060541927523664326974739203489792 71203732203657200101415190528000000000000 raw00002 affine00002
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00002_raw leaf00002_rectangular
    leaf00002_transform leaf00002_sign leaf00002_log
#print axioms leaf00002_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
