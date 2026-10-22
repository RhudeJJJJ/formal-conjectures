/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00071 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 32047775005002169590745137152000000000000 29976812895394797673249188620445042081792 1078418461852096472436279607296000000000000))
theorem leaf00071_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 32047775005002169590745137152000000000000 29976812895394797673249188620445042081792 1078418461852096472436279607296000000000000 raw00071=true := by decide +kernel
#print axioms leaf00071_raw
theorem leaf00071_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00071=true := by decide +kernel
#print axioms leaf00071_rectangular
def affine00071 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00071 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00071_transform : affine00071=(NestedInteger.clearedAll 3 raw00071 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00071_transform
theorem leaf00071_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00071=true := by decide +kernel
#print axioms leaf00071_sign
theorem leaf00071_log : RationalLog.accepts (977192427/1073741824) (-202338671/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00071_log
def leaf00071 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (27797013827/1000000000000) (977192427/1073741824) (-202338671/4294967296) 1 8 ![52,0,4] ![(3/400),0,(1/2)] ![(1/3200),1,(1/2)] affine00071
theorem leaf00071_checked : FastNestedCellData.accepts 1 0 4 leaf00071=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (27797013827/1000000000000) (977192427/1073741824) (-202338671/4294967296) 1 8 ![52,0,4] ![(3/400),0,(1/2)] ![(1/3200),1,(1/2)] 32047775005002169590745137152000000000000 29976812895394797673249188620445042081792 1078418461852096472436279607296000000000000 raw00071 affine00071
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00071_raw leaf00071_rectangular
    leaf00071_transform leaf00071_sign leaf00071_log
#print axioms leaf00071_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
